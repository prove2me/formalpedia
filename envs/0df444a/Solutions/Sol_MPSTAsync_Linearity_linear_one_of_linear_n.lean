-- Prove2me | solution 1 for MPSTAsync.Linearity.linear_one_of_linear_n
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T01:52:41.402238+00:00
-- url     : https://prove2.me/submissions/a0837fef-f0cb-4e41-9255-91bf4039a55f

import Definitions.Def_MPSTAsync_Linearity_Linearity

open MPSTAsync.Linearity

namespace SolMPSTLinearOne

inductive MuFree : GType → Prop where
  | comm {p q k U G} : MuFree G → MuFree (.comm p q k U G)
  | branch {p q k bs} : (∀ b ∈ bs, MuFree b.2) → MuFree (.branch p q k bs)
  | par {G H} : MuFree G → MuFree H → MuFree (.par G H)
  | var {t} : MuFree (.var t)
  | stop : MuFree .stop

theorem mem_substBranches_of_mem (t : TVar) (X : GType) :
    ∀ {bs : List (Label × GType)} {l : Label} {G : GType},
      (l, G) ∈ bs → (l, MPSTAsync.Linearity.subst t X G) ∈ MPSTAsync.Linearity.substBranches t X bs
  | [], _, _, h => by contradiction
  | (l', G') :: bs, l, G, h => by
    simp only [List.mem_cons] at h
    simp only [MPSTAsync.Linearity.substBranches, List.mem_cons]
    rcases h with h | h
    · cases h; exact .inl rfl
    · exact .inr (mem_substBranches_of_mem t X h)

theorem of_mem_substBranches (t : TVar) (X : GType) :
    ∀ {bs : List (Label × GType)} {l : Label} {G' : GType},
      (l, G') ∈ MPSTAsync.Linearity.substBranches t X bs →
      ∃ G, (l, G) ∈ bs ∧ G' = MPSTAsync.Linearity.subst t X G
  | [], _, _, h => by contradiction
  | (l₀, G₀) :: bs, l, G', h => by
    simp only [MPSTAsync.Linearity.substBranches, List.mem_cons] at h
    rcases h with h | h
    · cases h
      exact ⟨G₀, .head _, rfl⟩
    · obtain ⟨G, hmem, rfl⟩ := of_mem_substBranches t X h
      exact ⟨G, .tail _ hmem, rfl⟩

theorem MuFree.subst {t : TVar} {X : GType} (hX : MuFree X) :
    ∀ {G : GType}, MuFree G → MuFree (MPSTAsync.Linearity.subst t X G) := by
  intro G hG
  induction hG with
  | comm _ ih => exact .comm ih
  | branch _ ih =>
    apply MuFree.branch
    intro b hb
    rcases b with ⟨l, G'⟩
    obtain ⟨G₀, hmem₀, rfl⟩ := of_mem_substBranches t X hb
    exact ih (l, G₀) hmem₀
  | par _ _ ih₁ ih₂ => exact .par ih₁ ih₂
  | var =>
    unfold MPSTAsync.Linearity.subst
    split_ifs <;> [exact hX; exact .var]
  | stop => exact .stop

theorem MuFree.iter_subst {t : TVar} {B : GType} (hB : MuFree B) :
    ∀ m, MuFree ((fun X => MPSTAsync.Linearity.subst t X B)^[m] .stop)
  | 0 => .stop
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    exact MuFree.subst (MuFree.iter_subst hB m) hB

mutual
  theorem MuFree.unfold (n : ℕ) : (G : GType) → MuFree (MPSTAsync.Linearity.unfold n G)
    | .comm _ _ _ _ G => .comm (MuFree.unfold n G)
    | .branch _ _ _ bs => .branch (MuFree.unfoldBranches n bs)
    | .par G H => .par (MuFree.unfold n G) (MuFree.unfold n H)
    | .mu _ G => MuFree.iter_subst (MuFree.unfold n G) (n + 1)
    | .var _ => .var
    | .stop => .stop

  theorem MuFree.unfoldBranches (n : ℕ) :
      (bs : List (Label × GType)) →
      ∀ b ∈ MPSTAsync.Linearity.unfoldBranches n bs, MuFree b.2
    | [], _, hb => by contradiction
    | (_, G) :: bs, b, hb => by
      simp only [MPSTAsync.Linearity.unfoldBranches, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact MuFree.unfold n G
      · exact MuFree.unfoldBranches n bs b hb
end

@[simp] theorem label_stop (π : Position) : label .stop π = none := by
  cases π <;> simp [label, subterm]

@[simp] theorem label_var (t : TVar) (π : Position) : label (.var t) π = none := by
  cases π <;> simp [label, subterm]

@[simp] theorem label_comm_nil (p q : Role) (k : ℕ) (U : VType) (G : GType) :
    label (.comm p q k U G) [] = some (p, q, k) := rfl

@[simp] theorem label_comm_zero (p q : Role) (k : ℕ) (U : VType) (G : GType) (π : Position) :
    label (.comm p q k U G) (0 :: π) = label G π := rfl

@[simp] theorem label_branch_nil (p q : Role) (k : ℕ) (bs : List (Label × GType)) :
    label (.branch p q k bs) [] = some (p, q, k) := rfl

@[simp] theorem label_par_nil (G H : GType) : label (.par G H) [] = none := rfl

@[simp] theorem label_par_zero (G H : GType) (π : Position) :
    label (.par G H) (0 :: π) = label G π := rfl

@[simp] theorem label_par_one (G H : GType) (π : Position) :
    label (.par G H) (1 :: π) = label H π := rfl

theorem label_branch_cons (p q : Role) (k : ℕ) (bs : List (Label × GType)) (i : ℕ) (π : Position) :
    label (.branch p q k bs) (i :: π) =
      match bs[i]? with
      | some b => label b.2 π
      | none => none := by
  simp only [label, subterm]
  cases bs[i]? <;> rfl

theorem isNode_comm_cons {p q : Role} {k : ℕ} {U : VType} {G : GType} {c : ℕ} {π : Position}
    (h : IsNode (.comm p q k U G) (c :: π)) : c = 0 ∧ IsNode G π := by
  cases c with
  | zero => exact ⟨rfl, h⟩
  | succ c =>
    unfold IsNode label subterm at h
    simp at h

theorem isNode_branch_cons {p q : Role} {k : ℕ} {bs : List (Label × GType)} {i : ℕ} {π : Position}
    (h : IsNode (.branch p q k bs) (i :: π)) :
    ∃ l G, bs[i]? = some (l, G) ∧ IsNode G π := by
  unfold IsNode at h
  rw [label_branch_cons] at h
  cases hbs : bs[i]? with
  | none => simp [hbs] at h
  | some b =>
    rcases b with ⟨l, G⟩
    simp [hbs] at h
    exact ⟨l, G, rfl, h⟩

theorem isNode_par_cons {G H : GType} {c : ℕ} {π : Position}
    (h : IsNode (.par G H) (c :: π)) :
    (c = 0 ∧ IsNode G π) ∨ (c = 1 ∧ IsNode H π) := by
  rcases c with _ | _ | c
  · exact .inl ⟨rfl, h⟩
  · exact .inr ⟨rfl, h⟩
  · unfold IsNode label subterm at h
    simp at h

theorem precStep_to_strict_prefix {G : GType} {π ρ : Position} (h : PrecStep G π ρ) :
    IsNode G π ∧ IsNode G ρ ∧ ∃ d τ, ρ = π ++ d :: τ := by
  induction h with
  | commRoot hNode =>
    exact ⟨by simp [IsNode], hNode, 0, _, rfl⟩
  | branchRoot hbs hNode =>
    refine ⟨by simp [IsNode], ?_, _, _, rfl⟩
    unfold IsNode
    rw [label_branch_cons, hbs]
    exact hNode
  | commTail _ ih =>
    rcases ih with ⟨hπ, hρ, d, τ, rfl⟩
    exact ⟨hπ, hρ, d, τ, rfl⟩
  | branchTail hbs _ ih =>
    rcases ih with ⟨hπ, hρ, d, τ, rfl⟩
    refine ⟨?_, ?_, d, τ, rfl⟩
    · unfold IsNode; rw [label_branch_cons, hbs]; exact hπ
    · unfold IsNode; rw [label_branch_cons, hbs]; exact hρ
  | parLeft _ ih =>
    rcases ih with ⟨hπ, hρ, d, τ, rfl⟩
    exact ⟨hπ, hρ, d, τ, rfl⟩
  | parRight _ ih =>
    rcases ih with ⟨hπ, hρ, d, τ, rfl⟩
    exact ⟨hπ, hρ, d, τ, rfl⟩

theorem MuFree.precStep_of_strict_prefix {G : GType} (hG : MuFree G) :
    ∀ {π : Position} {d : ℕ} {τ : Position},
      IsNode G π → IsNode G (π ++ d :: τ) → PrecStep G π (π ++ d :: τ) := by
  induction hG with
  | comm _ ih =>
    intro π d τ hπ hρ
    cases π with
    | nil =>
      obtain ⟨rfl, hρ'⟩ := isNode_comm_cons hρ
      exact .commRoot hρ'
    | cons c π' =>
      obtain ⟨rfl, hπ'⟩ := isNode_comm_cons hπ
      obtain ⟨_, hρ'⟩ := isNode_comm_cons hρ
      exact .commTail (ih hπ' hρ')
  | branch _ ih =>
    intro π d τ hπ hρ
    cases π with
    | nil =>
      obtain ⟨l, G', hbs, hρ'⟩ := isNode_branch_cons hρ
      exact .branchRoot hbs hρ'
    | cons i π' =>
      obtain ⟨l, G', hbs, hπ'⟩ := isNode_branch_cons hπ
      obtain ⟨l₂, G₂, hbs₂, hρ'⟩ := isNode_branch_cons hρ
      rw [hbs] at hbs₂
      cases hbs₂
      exact .branchTail hbs (ih (l, G') (List.mem_of_getElem? hbs) hπ' hρ')
  | par _ _ ihG ihH =>
    intro π d τ hπ hρ
    cases π with
    | nil =>
      unfold IsNode at hπ
      simp at hπ
    | cons c π' =>
      rcases isNode_par_cons hπ with ⟨rfl, hπ'⟩ | ⟨rfl, hπ'⟩
      · exact .parLeft (ihG hπ' hρ)
      · exact .parRight (ihH hπ' hρ)
  | var =>
    intro π _ _ hπ _
    unfold IsNode at hπ
    simp at hπ
  | stop =>
    intro π _ _ hπ _
    unfold IsNode at hπ
    simp at hπ

theorem prec_to_strict_prefix {G : GType} {π ρ : Position} (h : Prec G π ρ) :
    IsNode G π ∧ IsNode G ρ ∧ ∃ d τ, ρ = π ++ d :: τ := by
  induction h with
  | single hstep => exact precStep_to_strict_prefix hstep
  | tail _ hstep ih =>
    rcases ih with ⟨hπ, _, d₁, τ₁, rfl⟩
    rcases precStep_to_strict_prefix hstep with ⟨_, hρ, d₂, τ₂, rfl⟩
    exact ⟨hπ, hρ, d₁, τ₁ ++ d₂ :: τ₂, by simp⟩

theorem MuFree.prec_iff {G : GType} (hG : MuFree G) {π ρ : Position} :
    Prec G π ρ ↔ IsNode G π ∧ IsNode G ρ ∧ ∃ d τ, ρ = π ++ d :: τ := by
  constructor
  · exact prec_to_strict_prefix
  · rintro ⟨hπ, hρ, d, τ, rfl⟩
    exact Relation.TransGen.single (hG.precStep_of_strict_prefix hπ hρ)

theorem prec_prefix_of {G : GType} {π ρ : Position} (h : Prec G π ρ) : π <+: ρ := by
  rcases prec_to_strict_prefix h with ⟨_, _, d, τ, rfl⟩
  exact List.prefix_append π (d :: τ)

mutual
  def Approx : GType → GType → Prop
    | .stop, _ => True
    | .var t, .var u => t = u
    | .comm p₁ q₁ k₁ U₁ G₁, .comm p₂ q₂ k₂ U₂ G₂ =>
        p₁ = p₂ ∧ q₁ = q₂ ∧ k₁ = k₂ ∧ U₁ = U₂ ∧ Approx G₁ G₂
    | .branch p₁ q₁ k₁ bs₁, .branch p₂ q₂ k₂ bs₂ =>
        p₁ = p₂ ∧ q₁ = q₂ ∧ k₁ = k₂ ∧ ApproxBranches bs₁ bs₂
    | .par G₁ H₁, .par G₂ H₂ => Approx G₁ G₂ ∧ Approx H₁ H₂
    | .mu t₁ G₁, .mu t₂ G₂ => t₁ = t₂ ∧ Approx G₁ G₂
    | _, _ => False

  def ApproxBranches : List (Label × GType) → List (Label × GType) → Prop
    | [], [] => True
    | (l₁, G₁) :: bs₁, (l₂, G₂) :: bs₂ =>
        l₁ = l₂ ∧ Approx G₁ G₂ ∧ ApproxBranches bs₁ bs₂
    | _, _ => False
end

mutual
  theorem approx_subst {t : TVar} {X₁ X₂ : GType} (hX : Approx X₁ X₂) :
      (G₁ G₂ : GType) → Approx G₁ G₂ →
      Approx (MPSTAsync.Linearity.subst t X₁ G₁) (MPSTAsync.Linearity.subst t X₂ G₂)
    | .stop, _, _ => trivial
    | .var u, .var v, h => by
      subst h
      unfold MPSTAsync.Linearity.subst
      split_ifs
      · exact hX
      · rfl
    | .comm _ _ _ _ G₁, .comm _ _ _ _ G₂, ⟨rfl, rfl, rfl, rfl, hG⟩ =>
      ⟨rfl, rfl, rfl, rfl, approx_subst hX G₁ G₂ hG⟩
    | .branch _ _ _ bs₁, .branch _ _ _ bs₂, ⟨rfl, rfl, rfl, hbs⟩ =>
      ⟨rfl, rfl, rfl, approxBranches_subst hX bs₁ bs₂ hbs⟩
    | .par G₁ H₁, .par G₂ H₂, ⟨hG, hH⟩ =>
      ⟨approx_subst hX G₁ G₂ hG, approx_subst hX H₁ H₂ hH⟩
    | .mu u₁ G₁, .mu u₂ G₂, ⟨h₁, hG⟩ => by
      subst h₁
      unfold MPSTAsync.Linearity.subst
      split_ifs
      · exact ⟨rfl, hG⟩
      · exact ⟨rfl, approx_subst hX G₁ G₂ hG⟩

  theorem approxBranches_subst {t : TVar} {X₁ X₂ : GType} (hX : Approx X₁ X₂) :
      (bs₁ bs₂ : List (Label × GType)) → ApproxBranches bs₁ bs₂ →
      ApproxBranches (MPSTAsync.Linearity.substBranches t X₁ bs₁)
        (MPSTAsync.Linearity.substBranches t X₂ bs₂)
    | [], [], _ => trivial
    | (_, G₁) :: bs₁, (_, G₂) :: bs₂, ⟨hl, hG, hbs⟩ =>
      ⟨hl, approx_subst hX G₁ G₂ hG, approxBranches_subst hX bs₁ bs₂ hbs⟩
end

theorem approx_iter_subst {t : TVar} {B₁ B₂ : GType} (hB : Approx B₁ B₂) :
    ∀ {m n : ℕ}, m ≤ n →
      Approx ((fun X => MPSTAsync.Linearity.subst t X B₁)^[m] .stop)
             ((fun X => MPSTAsync.Linearity.subst t X B₂)^[n] .stop)
  | 0, _, _ => trivial
  | m + 1, n + 1, hmn => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact approx_subst (approx_iter_subst hB (Nat.le_of_succ_le_succ hmn)) B₁ B₂ hB

mutual
  theorem approx_unfold {m n : ℕ} (hmn : m ≤ n) :
      (G : GType) → Approx (MPSTAsync.Linearity.unfold m G) (MPSTAsync.Linearity.unfold n G)
    | .comm _ _ _ _ G => ⟨rfl, rfl, rfl, rfl, approx_unfold hmn G⟩
    | .branch _ _ _ bs => ⟨rfl, rfl, rfl, approxBranches_unfold hmn bs⟩
    | .par G H => ⟨approx_unfold hmn G, approx_unfold hmn H⟩
    | .mu _ G => approx_iter_subst (approx_unfold hmn G) (Nat.succ_le_succ hmn)
    | .var _ => rfl
    | .stop => trivial

  theorem approxBranches_unfold {m n : ℕ} (hmn : m ≤ n) :
      (bs : List (Label × GType)) →
      ApproxBranches (MPSTAsync.Linearity.unfoldBranches m bs)
        (MPSTAsync.Linearity.unfoldBranches n bs)
    | [] => trivial
    | (_, G) :: bs => ⟨rfl, approx_unfold hmn G, approxBranches_unfold hmn bs⟩
end

mutual
  theorem approx_label_eq_of_isNode :
      (H₁ H₂ : GType) → Approx H₁ H₂ →
      ∀ {σ ρ : Position}, σ <+: ρ → IsNode H₁ ρ → label H₁ σ = label H₂ σ
    | .stop, _, _, _, _, _, hρ => by
      unfold IsNode at hρ; simp at hρ
    | .var _, .var _, _, _, _, _, hρ => by
      unfold IsNode at hρ; simp at hρ
    | .comm _ _ _ _ G₁, .comm _ _ _ _ G₂, ⟨rfl, rfl, rfl, rfl, hG⟩, σ, ρ, hσρ, hρ => by
      cases σ with
      | nil => rfl
      | cons c σ' =>
        rcases hσρ with ⟨δ, rfl⟩
        obtain ⟨rfl, hρ'⟩ := isNode_comm_cons hρ
        exact approx_label_eq_of_isNode G₁ G₂ hG ⟨δ, rfl⟩ hρ'
    | .branch _ _ _ bs₁, .branch _ _ _ bs₂, ⟨rfl, rfl, rfl, hbs⟩, σ, ρ, hσρ, hρ => by
      cases σ with
      | nil => rfl
      | cons i σ' =>
        rcases hσρ with ⟨δ, rfl⟩
        obtain ⟨l, G₁, hbs₁, hρ'⟩ := isNode_branch_cons hρ
        rw [label_branch_cons, label_branch_cons]
        exact approxBranches_label_eq_of_isNode bs₁ bs₂ hbs i l G₁ hbs₁ ⟨δ, rfl⟩ hρ'
    | .par G₁ K₁, .par G₂ K₂, ⟨hG, hK⟩, σ, ρ, hσρ, hρ => by
      cases σ with
      | nil => rfl
      | cons c σ' =>
        rcases hσρ with ⟨δ, rfl⟩
        rcases isNode_par_cons hρ with ⟨rfl, hρ'⟩ | ⟨rfl, hρ'⟩
        · exact approx_label_eq_of_isNode G₁ G₂ hG ⟨δ, rfl⟩ hρ'
        · exact approx_label_eq_of_isNode K₁ K₂ hK ⟨δ, rfl⟩ hρ'
    | .mu _ G₁, .mu _ G₂, ⟨rfl, hG⟩, σ, ρ, hσρ, hρ => by
      cases σ with
      | nil => rfl
      | cons c σ' =>
        rcases hσρ with ⟨δ, rfl⟩
        cases c with
        | zero => exact approx_label_eq_of_isNode G₁ G₂ hG ⟨δ, rfl⟩ hρ
        | succ c =>
          unfold IsNode label subterm at hρ
          simp at hρ

  theorem approxBranches_label_eq_of_isNode :
      (bs₁ bs₂ : List (Label × GType)) → ApproxBranches bs₁ bs₂ →
      ∀ (i : ℕ) (l : Label) (G₁ : GType), bs₁[i]? = some (l, G₁) →
      ∀ {σ ρ : Position}, σ <+: ρ → IsNode G₁ ρ →
      (match bs₁[i]? with | some b => label b.2 σ | none => none) =
      (match bs₂[i]? with | some b => label b.2 σ | none => none)
    | [], [], _, i, _, _, hbs₁, _, _, _, _ => by simp at hbs₁
    | (l₁, G₁') :: bs₁, (l₂, G₂') :: bs₂, ⟨_, hG, hbs⟩, i, l, G₁, hbs₁, σ, ρ, hσρ, hρ => by
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at hbs₁ ⊢
        cases hbs₁
        exact approx_label_eq_of_isNode G₁' G₂' hG hσρ hρ
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbs₁ ⊢
        exact approxBranches_label_eq_of_isNode bs₁ bs₂ hbs i l G₁ hbs₁ hσρ hρ
end

theorem approx_prec_of_node {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) {α β ρ : Position}
    (hβρ : β <+: ρ) (hρ : IsNode H₁ ρ) :
    Prec H₁ α β ↔ Prec H₂ α β := by
  rw [h₁.prec_iff, h₂.prec_iff]
  constructor
  · rintro ⟨hα, hβ, d, τ, rfl⟩
    have hαβ : α <+: α ++ d :: τ := List.prefix_append α (d :: τ)
    have hαρ : α <+: ρ := hαβ.trans hβρ
    have hlblα := approx_label_eq_of_isNode H₁ H₂ h hαρ hρ
    have hlblβ := approx_label_eq_of_isNode H₁ H₂ h hβρ hρ
    unfold IsNode at hα hβ ⊢
    rw [← hlblα, ← hlblβ]
    exact ⟨hα, hβ, d, τ, rfl⟩
  · rintro ⟨hα, hβ, d, τ, rfl⟩
    have hαβ : α <+: α ++ d :: τ := List.prefix_append α (d :: τ)
    have hαρ : α <+: ρ := hαβ.trans hβρ
    have hlblα := approx_label_eq_of_isNode H₁ H₂ h hαρ hρ
    have hlblβ := approx_label_eq_of_isNode H₁ H₂ h hβρ hρ
    unfold IsNode at hα hβ ⊢
    rw [hlblα, hlblβ]
    exact ⟨hα, hβ, d, τ, rfl⟩

theorem approx_precIO_of_node {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) {α β ρ : Position}
    (hβρ : β <+: ρ) (hρ : IsNode H₁ ρ) (hstep : PrecIO H₂ α β) :
    PrecIO H₁ α β := by
  rcases hstep with ⟨hprec, p, q, r, k₁, k₂, hα, hβ⟩
  have hαβ : α <+: β := prec_prefix_of hprec
  have hαρ : α <+: ρ := hαβ.trans hβρ
  refine ⟨(approx_prec_of_node h h₁ h₂ hβρ hρ).mpr hprec, p, q, r, k₁, k₂, ?_, ?_⟩
  · rw [approx_label_eq_of_isNode H₁ H₂ h hαρ hρ]; exact hα
  · rw [approx_label_eq_of_isNode H₁ H₂ h hβρ hρ]; exact hβ

theorem approx_precOO_of_node {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) {α β ρ : Position}
    (hβρ : β <+: ρ) (hρ : IsNode H₁ ρ) (hstep : PrecOO H₂ α β) :
    PrecOO H₁ α β := by
  rcases hstep with ⟨hprec, p, q₁, q₂, k, hα, hβ⟩
  have hαβ : α <+: β := prec_prefix_of hprec
  have hαρ : α <+: ρ := hαβ.trans hβρ
  refine ⟨(approx_prec_of_node h h₁ h₂ hβρ hρ).mpr hprec, p, q₁, q₂, k, ?_, ?_⟩
  · rw [approx_label_eq_of_isNode H₁ H₂ h hαρ hρ]; exact hα
  · rw [approx_label_eq_of_isNode H₁ H₂ h hβρ hρ]; exact hβ

theorem approx_precII_of_node {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) {α β ρ : Position}
    (hβρ : β <+: ρ) (hρ : IsNode H₁ ρ) (hstep : PrecII H₂ α β) :
    PrecII H₁ α β := by
  rcases hstep with ⟨hprec, p₁, p₂, q, k₁, k₂, hα, hβ⟩
  have hαβ : α <+: β := prec_prefix_of hprec
  have hαρ : α <+: ρ := hαβ.trans hβρ
  refine ⟨(approx_prec_of_node h h₁ h₂ hβρ hρ).mpr hprec, p₁, p₂, q, k₁, k₂, ?_, ?_⟩
  · rw [approx_label_eq_of_isNode H₁ H₂ h hαρ hρ]; exact hα
  · rw [approx_label_eq_of_isNode H₁ H₂ h hβρ hρ]; exact hβ

theorem approx_reflTransGen_precIO_of_node {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) {π σ ρ : Position}
    (hρ : IsNode H₁ ρ) (hchain : Relation.ReflTransGen (PrecIO H₂) π σ) (hσρ : σ <+: ρ) :
    Relation.ReflTransGen (PrecIO H₁) π σ := by
  induction hchain with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    have hbρ : b <+: ρ := (prec_prefix_of hbc.1).trans hσρ
    exact .tail (ih hbρ) (approx_precIO_of_node h h₁ h₂ hσρ hρ hbc)

theorem approx_outputDep_of_node {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) {π σ ρ : Position}
    (hρ : IsNode H₁ ρ) (hchain : OutputDep H₂ π σ) (hσρ : σ <+: ρ) :
    OutputDep H₁ π σ := by
  induction hchain with
  | @single b hstep =>
    apply Relation.TransGen.single
    rcases hstep with hOO | hIO
    · exact .inl (approx_precOO_of_node h h₁ h₂ hσρ hρ hOO)
    · exact .inr (approx_precIO_of_node h h₁ h₂ hσρ hρ hIO)
  | @tail b c _ hbc ih =>
    have hbρ : b <+: ρ := by
      rcases hbc with hOO | hIO
      · exact (prec_prefix_of hOO.1).trans hσρ
      · exact (prec_prefix_of hIO.1).trans hσρ
    apply Relation.TransGen.tail (ih hbρ)
    rcases hbc with hOO | hIO
    · exact .inl (approx_precOO_of_node h h₁ h₂ hσρ hρ hOO)
    · exact .inr (approx_precIO_of_node h h₁ h₂ hσρ hρ hIO)

theorem approx_mainLinear {H₁ H₂ : GType} (h : Approx H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) (hlin : MainLinear H₂) :
    MainLinear H₁ := by
  intro π ρ p₁ q₁ p₂ q₂ k hprec hlblπ hlblρ
  have hρ : IsNode H₁ ρ := by unfold IsNode; simp [hlblρ]
  have hπρ : π <+: ρ := prec_prefix_of hprec
  have hprec₂ : Prec H₂ π ρ := (approx_prec_of_node h h₁ h₂ (List.prefix_refl ρ) hρ).mp hprec
  have hlblπ₂ : label H₂ π = some (p₁, q₁, k) := by
    rw [← approx_label_eq_of_isNode H₁ H₂ h hπρ hρ]; exact hlblπ
  have hlblρ₂ : label H₂ ρ = some (p₂, q₂, k) := by
    rw [← approx_label_eq_of_isNode H₁ H₂ h (List.prefix_refl ρ) hρ]; exact hlblρ
  obtain ⟨⟨σ, hIO, hII⟩, hOut⟩ := hlin π ρ p₁ q₁ p₂ q₂ k hprec₂ hlblπ₂ hlblρ₂
  have hσρ : σ <+: ρ := prec_prefix_of hII.1
  refine ⟨⟨σ, approx_reflTransGen_precIO_of_node h h₁ h₂ hρ hIO hσρ,
    approx_precII_of_node h h₁ h₂ (List.prefix_refl ρ) hρ hII⟩,
    approx_outputDep_of_node h h₁ h₂ hρ hOut (List.prefix_refl ρ)⟩

theorem directCarried_subst_right {t : TVar} {X G H : GType} (h : DirectCarried G H) :
    DirectCarried (MPSTAsync.Linearity.subst t X G) H := by
  induction h with
  | commValue hV => exact .commValue hV
  | commTail _ ih => exact .commTail ih
  | branchBody hmem _ ih =>
    exact .branchBody (mem_substBranches_of_mem t X hmem) ih
  | parLeft _ ih => exact .parLeft ih
  | parRight _ ih => exact .parRight ih
  | muBody hG ih =>
    unfold MPSTAsync.Linearity.subst
    split_ifs
    · exact .muBody hG
    · exact .muBody ih

mutual
  theorem directCarried_of_subst (t : TVar) (X : GType) :
      (G : GType) → ∀ {H : GType},
      DirectCarried (MPSTAsync.Linearity.subst t X G) H →
      DirectCarried G H ∨ DirectCarried X H
    | .comm _ _ _ _ G, _, h => by
      cases h with
      | commValue hV => exact .inl (.commValue hV)
      | commTail hG =>
        rcases directCarried_of_subst t X G hG with hG | hX
        · exact .inl (.commTail hG)
        · exact .inr hX
    | .branch _ _ _ bs, _, h => by
      cases h with
      | branchBody hmem hG' =>
        rcases directCarriedBranches_of_subst t X bs hmem hG' with ⟨l₀, G₀, hmem₀, hG₀⟩ | hX
        · exact .inl (.branchBody hmem₀ hG₀)
        · exact .inr hX
    | .par G₁ G₂, _, h => by
      cases h with
      | parLeft h₁ =>
        rcases directCarried_of_subst t X G₁ h₁ with h₁ | hX
        · exact .inl (.parLeft h₁)
        · exact .inr hX
      | parRight h₂ =>
        rcases directCarried_of_subst t X G₂ h₂ with h₂ | hX
        · exact .inl (.parRight h₂)
        · exact .inr hX
    | .mu u G, _, h => by
      unfold MPSTAsync.Linearity.subst at h
      split_ifs at h
      · exact .inl h
      · cases h with
        | muBody hG =>
          rcases directCarried_of_subst t X G hG with hG | hX
          · exact .inl (.muBody hG)
          · exact .inr hX
    | .var u, _, h => by
      unfold MPSTAsync.Linearity.subst at h
      split_ifs at h
      · exact .inr h
      · cases h
    | .stop, _, h => by cases h

  theorem directCarriedBranches_of_subst (t : TVar) (X : GType) :
      (bs : List (Label × GType)) → ∀ {l : Label} {G' H : GType},
      (l, G') ∈ MPSTAsync.Linearity.substBranches t X bs →
      DirectCarried G' H →
      (∃ l₀ G₀, (l₀, G₀) ∈ bs ∧ DirectCarried G₀ H) ∨ DirectCarried X H
    | [], _, _, _, hmem, _ => by contradiction
    | (l₀, G₀) :: bs, l, G', H, hmem, hG' => by
      simp only [MPSTAsync.Linearity.substBranches, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        rcases directCarried_of_subst t X G₀ hG' with hG₀ | hX
        · exact .inl ⟨l₀, G₀, .head _, hG₀⟩
        · exact .inr hX
      · rcases directCarriedBranches_of_subst t X bs htail hG' with ⟨l₁, G₁, hmem₁, hG₁⟩ | hX
        · exact .inl ⟨l₁, G₁, .tail _ hmem₁, hG₁⟩
        · exact .inr hX
end

theorem directCarried_of_iter_subst {t : TVar} {B H : GType} :
    ∀ m, DirectCarried ((fun X => MPSTAsync.Linearity.subst t X B)^[m] .stop) H →
      DirectCarried B H
  | 0, h => by cases h
  | m + 1, h => by
    rw [Function.iterate_succ_apply'] at h
    rcases directCarried_of_subst t _ B h with hB | hm
    · exact hB
    · exact directCarried_of_iter_subst m hm

theorem mem_unfoldBranches_of_mem (n : ℕ) :
    ∀ {bs : List (Label × GType)} {l : Label} {G : GType},
      (l, G) ∈ bs → (l, MPSTAsync.Linearity.unfold n G) ∈ MPSTAsync.Linearity.unfoldBranches n bs
  | [], _, _, h => by contradiction
  | (l', G') :: bs, l, G, h => by
    simp only [List.mem_cons] at h
    simp only [MPSTAsync.Linearity.unfoldBranches, List.mem_cons]
    rcases h with h | h
    · cases h; exact .inl rfl
    · exact .inr (mem_unfoldBranches_of_mem n h)

theorem directCarried_unfold (n : ℕ) {G H : GType} (h : DirectCarried G H) :
    DirectCarried (MPSTAsync.Linearity.unfold n G) H := by
  induction h with
  | commValue hV => exact .commValue hV
  | commTail _ ih => exact .commTail ih
  | branchBody hmem _ ih =>
    exact .branchBody (mem_unfoldBranches_of_mem n hmem) ih
  | parLeft _ ih => exact .parLeft ih
  | parRight _ ih => exact .parRight ih
  | muBody _ ih =>
    unfold MPSTAsync.Linearity.unfold
    rw [Function.iterate_succ_apply']
    exact directCarried_subst_right ih

mutual
  theorem directCarried_of_unfold (n : ℕ) :
      (G : GType) → ∀ {H : GType},
      DirectCarried (MPSTAsync.Linearity.unfold n G) H → DirectCarried G H
    | .comm _ _ _ _ G, _, h => by
      cases h with
      | commValue hV => exact .commValue hV
      | commTail hG => exact .commTail (directCarried_of_unfold n G hG)
    | .branch _ _ _ bs, _, h => by
      cases h with
      | branchBody hmem hG' =>
        obtain ⟨l₀, G₀, hmem₀, hG₀⟩ := directCarriedBranches_of_unfold n bs hmem hG'
        exact .branchBody hmem₀ hG₀
    | .par G₁ G₂, _, h => by
      cases h with
      | parLeft h₁ => exact .parLeft (directCarried_of_unfold n G₁ h₁)
      | parRight h₂ => exact .parRight (directCarried_of_unfold n G₂ h₂)
    | .mu _ G, _, h =>
      .muBody (directCarried_of_unfold n G (directCarried_of_iter_subst (n + 1) h))
    | .var _, _, h => h
    | .stop, _, h => h

  theorem directCarriedBranches_of_unfold (n : ℕ) :
      (bs : List (Label × GType)) → ∀ {l : Label} {G' H : GType},
      (l, G') ∈ MPSTAsync.Linearity.unfoldBranches n bs →
      DirectCarried G' H →
      ∃ l₀ G₀, (l₀, G₀) ∈ bs ∧ DirectCarried G₀ H
    | [], _, _, _, hmem, _ => by contradiction
    | (l₀, G₀) :: bs, l, G', H, hmem, hG' => by
      simp only [MPSTAsync.Linearity.unfoldBranches, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        exact ⟨l₀, G₀, .head _, directCarried_of_unfold n G₀ hG'⟩
      · obtain ⟨l₁, G₁, hmem₁, hG₁⟩ := directCarriedBranches_of_unfold n bs htail hG'
        exact ⟨l₁, G₁, .tail _ hmem₁, hG₁⟩
end

theorem carried_of_first {G₁ G₂ H : GType}
    (hstep : ∀ K, DirectCarried G₁ K → DirectCarried G₂ K)
    (h : Carried G₁ H) : Carried G₂ H := by
  induction h with
  | single h₁ => exact .single (hstep _ h₁)
  | tail _ h₂ ih => exact .tail ih h₂

theorem carried_unfold_iff (n : ℕ) (G H : GType) :
    Carried (MPSTAsync.Linearity.unfold n G) H ↔ Carried G H :=
  ⟨carried_of_first (fun _ => directCarried_of_unfold n G),
   carried_of_first (fun _ => directCarried_unfold n)⟩

end SolMPSTLinearOne

theorem solution (G : GType) (_hG : WellFormed G) (n : ℕ) (hn : 1 ≤ n) :
    Linear (unfold n G) → Linear (unfold 1 G) := by
  rintro ⟨hMain, hCarried⟩
  refine ⟨?_, ?_⟩
  · exact SolMPSTLinearOne.approx_mainLinear
      (SolMPSTLinearOne.approx_unfold hn G)
      (SolMPSTLinearOne.MuFree.unfold 1 G)
      (SolMPSTLinearOne.MuFree.unfold n G) hMain
  · intro H hH m
    apply hCarried H
    rwa [SolMPSTLinearOne.carried_unfold_iff, ← SolMPSTLinearOne.carried_unfold_iff 1]
