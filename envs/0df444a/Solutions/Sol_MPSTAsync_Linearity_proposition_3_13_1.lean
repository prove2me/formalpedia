-- Prove2me | solution 1 for MPSTAsync.Linearity.proposition_3_13_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T02:23:39.054595+00:00
-- url     : https://prove2.me/submissions/4496657d-aacf-4999-87c0-ae9d78d58314

import Definitions.Def_MPSTAsync_Linearity_Linearity

open MPSTAsync.Linearity

namespace SolMPSTProp3131

abbrev Label3 := Role × Role × ℕ

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

theorem getElem?_substBranches (t : TVar) (X : GType) (bs : List (Label × GType)) (i : ℕ) :
    (MPSTAsync.Linearity.substBranches t X bs)[i]? =
      (bs[i]?).map (fun b => (b.1, MPSTAsync.Linearity.subst t X b.2)) := by
  induction bs generalizing i with
  | nil => simp [MPSTAsync.Linearity.substBranches]
  | cons b bs ih =>
    rcases b with ⟨l, G⟩
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getElem?_unfoldBranches (n : ℕ) (bs : List (Label × GType)) (i : ℕ) :
    (MPSTAsync.Linearity.unfoldBranches n bs)[i]? =
      (bs[i]?).map (fun b => (b.1, MPSTAsync.Linearity.unfold n b.2)) := by
  induction bs generalizing i with
  | nil => simp [MPSTAsync.Linearity.unfoldBranches]
  | cons b bs ih =>
    rcases b with ⟨l, G⟩
    cases i with
    | zero => rfl
    | succ i => exact ih i

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

/-! ### Prefix approximation `Approx` (for the `n → 1` direction) -/

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

/-! ### Invariance of `Carried` under `unfold` -/

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

/-! ### Label Traces, `halfOpenLabels`, and `TraceSim` (for the `1 → n` direction) -/

inductive EndKind where
  | node (l : Label3)
  | var (t : TVar)
  deriving DecidableEq

def endKind (G : GType) (π : Position) : Option EndKind :=
  match subterm G π with
  | some (.comm p q k _ _) => some (.node (p, q, k))
  | some (.branch p q k _) => some (.node (p, q, k))
  | some (.var t) => some (.var t)
  | _ => none

theorem endKind_eq_node_iff {G : GType} {π : Position} {l : Label3} :
    endKind G π = some (.node l) ↔ label G π = some l := by
  unfold endKind label
  cases subterm G π with
  | none => simp
  | some K => cases K <;> simp

theorem endKind_eq_var_iff {G : GType} {π : Position} {t : TVar} :
    endKind G π = some (.var t) ↔ subterm G π = some (.var t) := by
  unfold endKind
  cases subterm G π with
  | none => simp
  | some K => cases K <;> simp

local infix:50 " <+ " => List.Sublist

theorem subterm_isSome_of_endKind_eq_some {G : GType} {π : Position} {ek : EndKind}
    (h : endKind G π = some ek) : (subterm G π).isSome := by
  unfold endKind at h
  cases hsub : subterm G π with
  | none => simp [hsub] at h
  | some _ => rfl

theorem subterm_isSome_of_label_eq_some {G : GType} {π : Position} {l : Label3}
    (h : label G π = some l) : (subterm G π).isSome := by
  unfold label at h
  cases hsub : subterm G π with
  | none => simp [hsub] at h
  | some _ => rfl

def halfOpenLabels (G : GType) (base : Position) : Position → List Label3
  | [] => []
  | d :: τ =>
      (match label G base with
       | some l => [l]
       | none => []) ++ halfOpenLabels G (base ++ [d]) τ

theorem halfOpenLabels_append (G : GType) (base δ₁ δ₂ : Position) :
    halfOpenLabels G base (δ₁ ++ δ₂) =
      halfOpenLabels G base δ₁ ++ halfOpenLabels G (base ++ δ₁) δ₂ := by
  induction δ₁ generalizing base with
  | nil => simp [halfOpenLabels]
  | cons d τ ih =>
    simp only [List.cons_append, halfOpenLabels, List.append_assoc]
    rw [ih (base ++ [d])]
    simp [List.append_assoc]

theorem halfOpenLabels_congr {G₁ G₂ : GType} {base₁ base₂ δ : Position}
    (h : ∀ δ' d τ, δ = δ' ++ d :: τ → label G₁ (base₁ ++ δ') = label G₂ (base₂ ++ δ')) :
    halfOpenLabels G₁ base₁ δ = halfOpenLabels G₂ base₂ δ := by
  induction δ generalizing base₁ base₂ with
  | nil => rfl
  | cons d τ ih =>
    simp only [halfOpenLabels]
    have h0 : label G₁ base₁ = label G₂ base₂ := by
      simpa using h [] d τ rfl
    rw [h0]
    congr 1
    apply ih
    intro δ' d' τ' hτ
    have hfull : d :: τ = (d :: δ') ++ d' :: τ' := by simp [hτ]
    simpa [List.append_assoc] using h (d :: δ') d' τ' hfull

def isIO (a b : Label3) : Prop := a.2.1 = b.1
def isOO (a b : Label3) : Prop := a.1 = b.1 ∧ a.2.2 = b.2.2
def isII (a b : Label3) : Prop := a.2.1 = b.2.1

theorem isIO_iff {G : GType} {α β : Position} {a b : Label3}
    (hα : label G α = some a) (hβ : label G β = some b) :
    (∃ p q r k₁ k₂, label G α = some (p, q, k₁) ∧ label G β = some (q, r, k₂)) ↔ isIO a b := by
  rcases a with ⟨p₁, q₁, k₁⟩
  rcases b with ⟨p₂, q₂, k₂⟩
  rw [hα, hβ]
  unfold isIO
  constructor
  · rintro ⟨p, q, r, k₁', k₂', h₁, h₂⟩
    cases h₁; cases h₂; rfl
  · intro h
    subst h
    exact ⟨p₁, q₁, q₂, k₁, k₂, rfl, rfl⟩

theorem isOO_iff {G : GType} {α β : Position} {a b : Label3}
    (hα : label G α = some a) (hβ : label G β = some b) :
    (∃ p q₁ q₂ k, label G α = some (p, q₁, k) ∧ label G β = some (p, q₂, k)) ↔ isOO a b := by
  rcases a with ⟨p₁, q₁, k₁⟩
  rcases b with ⟨p₂, q₂, k₂⟩
  rw [hα, hβ]
  unfold isOO
  constructor
  · rintro ⟨p, q₁', q₂', k, h₁, h₂⟩
    cases h₁; cases h₂; exact ⟨rfl, rfl⟩
  · rintro ⟨hp, hk⟩
    subst hp; subst hk
    exact ⟨p₁, q₁, q₂, k₁, rfl, rfl⟩

theorem isII_iff {G : GType} {α β : Position} {a b : Label3}
    (hα : label G α = some a) (hβ : label G β = some b) :
    (∃ p₁ p₂ q k₁ k₂, label G α = some (p₁, q, k₁) ∧ label G β = some (p₂, q, k₂)) ↔ isII a b := by
  rcases a with ⟨p₁, q₁, k₁⟩
  rcases b with ⟨p₂, q₂, k₂⟩
  rw [hα, hβ]
  unfold isII
  constructor
  · rintro ⟨p₁', p₂', q, k₁', k₂', h₁, h₂⟩
    cases h₁; cases h₂; rfl
  · intro h
    subst h
    exact ⟨p₁, p₂, q₁, k₁, k₂, rfl, rfl⟩

def TraceInputDep (a : Label3) : List Label3 → Label3 → Prop
  | [], b => isII a b
  | x :: xs, b => TraceInputDep a xs b ∨ (isIO a x ∧ TraceInputDep x xs b)

def TraceOutputDep (a : Label3) : List Label3 → Label3 → Prop
  | [], b => isOO a b ∨ isIO a b
  | x :: xs, b => TraceOutputDep a xs b ∨ ((isOO a x ∨ isIO a x) ∧ TraceOutputDep x xs b)

theorem TraceInputDep.sublist {tr₁ tr₂ : List Label3} (hsub : tr₁ <+ tr₂) :
    ∀ {a b : Label3}, TraceInputDep a tr₁ b → TraceInputDep a tr₂ b := by
  induction hsub with
  | slnil => intro _ _ h; exact h
  | cons _ _ ih => intro _ _ h; exact .inl (ih h)
  | cons_cons _ _ ih =>
    intro _ _ h
    rcases h with h | ⟨hIO, h⟩
    · exact .inl (ih h)
    · exact .inr ⟨hIO, ih h⟩

theorem TraceOutputDep.sublist {tr₁ tr₂ : List Label3} (hsub : tr₁ <+ tr₂) :
    ∀ {a b : Label3}, TraceOutputDep a tr₁ b → TraceOutputDep a tr₂ b := by
  induction hsub with
  | slnil => intro _ _ h; exact h
  | cons _ _ ih => intro _ _ h; exact .inl (ih h)
  | cons_cons _ _ ih =>
    intro _ _ h
    rcases h with h | ⟨hstep, h⟩
    · exact .inl (ih h)
    · exact .inr ⟨hstep, ih h⟩

theorem reflTransGen_precIO_prefix {G : GType} {α β : Position}
    (h : Relation.ReflTransGen (PrecIO G) α β) : α <+: β := by
  induction h with
  | refl => exact List.prefix_refl _
  | tail _ hstep ih => exact ih.trans (prec_prefix_of hstep.1)

theorem strict_prefix_of_prefix_of_prec {G : GType} {b σ ρ : Position}
    (h₁ : b <+: σ) (h₂ : Prec G σ ρ) : ∃ d₂ τ₂, ρ = b ++ d₂ :: τ₂ := by
  rcases h₁ with ⟨δ, rfl⟩
  rcases prec_to_strict_prefix h₂ with ⟨_, _, d, τ, rfl⟩
  cases δ with
  | nil => exact ⟨d, τ, by simp⟩
  | cons d₀ δ' => exact ⟨d₀, δ' ++ d :: τ, by simp⟩

theorem outputDep_prefix {G : GType} {α β : Position}
    (h : OutputDep G α β) : α <+: β := by
  induction h with
  | single hstep =>
    rcases hstep with hOO | hIO
    · exact prec_prefix_of hOO.1
    · exact prec_prefix_of hIO.1
  | tail _ hstep ih =>
    rcases hstep with hOO | hIO
    · exact ih.trans (prec_prefix_of hOO.1)
    · exact ih.trans (prec_prefix_of hIO.1)

theorem strict_prefix_of_outputDep {G : GType} {b ρ : Position}
    (h : OutputDep G b ρ) : ∃ d₂ τ₂, ρ = b ++ d₂ :: τ₂ := by
  induction h using Relation.TransGen.head_induction_on with
  | single hstep =>
    rcases hstep with hOO | hIO
    · rcases prec_to_strict_prefix hOO.1 with ⟨_, _, d, τ, rfl⟩
      exact ⟨d, τ, rfl⟩
    · rcases prec_to_strict_prefix hIO.1 with ⟨_, _, d, τ, rfl⟩
      exact ⟨d, τ, rfl⟩
  | @head a c hac hcr _ =>
    have hstep_prec : Prec G a c := by
      rcases hac with hOO | hIO
      · exact hOO.1
      · exact hIO.1
    rcases prec_to_strict_prefix hstep_prec with ⟨_, _, d₁, τ₁, rfl⟩
    rcases outputDep_prefix hcr with ⟨δ, rfl⟩
    exact ⟨d₁, τ₁ ++ δ, by simp⟩

theorem traceInputDep_of_reflTransGen_precIO {G : GType} {π σ : Position}
    (hIO : Relation.ReflTransGen (PrecIO G) π σ) :
    ∀ {d : ℕ} {τ : Position} {l_π l_ρ : Label3},
      PrecII G σ (π ++ d :: τ) →
      label G π = some l_π →
      label G (π ++ d :: τ) = some l_ρ →
      TraceInputDep l_π (halfOpenLabels G (π ++ [d]) τ) l_ρ := by
  induction hIO using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro d τ l_π l_ρ hII hπ hρ
    have hbase : TraceInputDep l_π [] l_ρ := (isII_iff hπ hρ).mp hII.2
    exact TraceInputDep.sublist (List.nil_sublist _) hbase
  | @head a b hab hbc ih =>
    intro d τ l_a l_ρ hII ha hρ
    rcases prec_to_strict_prefix hab.1 with ⟨_, hbNode, d₁, τ₁, rfl⟩
    unfold IsNode at hbNode
    rcases Option.isSome_iff_exists.mp hbNode with ⟨l_b, hb⟩
    have hIO_ab : isIO l_a l_b := (isIO_iff ha hb).mp hab.2
    obtain ⟨d₂, τ₂, hρ_eq⟩ := strict_prefix_of_prefix_of_prec (reflTransGen_precIO_prefix hbc) hII.1
    have hρ_eq' : d = d₁ ∧ τ = τ₁ ++ d₂ :: τ₂ := by
      simpa [List.append_assoc] using hρ_eq
    rcases hρ_eq' with ⟨hd, rfl⟩
    subst d
    have hII' : PrecII G σ ((a ++ d₁ :: τ₁) ++ d₂ :: τ₂) := by
      simpa [List.append_assoc] using hII
    have hρ' : label G ((a ++ d₁ :: τ₁) ++ d₂ :: τ₂) = some l_ρ := by
      simpa [List.append_assoc] using hρ
    have ih_res := ih hII' hb hρ'
    have hsplit :
        halfOpenLabels G (a ++ [d₁]) (τ₁ ++ d₂ :: τ₂) =
          halfOpenLabels G (a ++ [d₁]) τ₁ ++
            (l_b :: halfOpenLabels G ((a ++ d₁ :: τ₁) ++ [d₂]) τ₂) := by
      rw [halfOpenLabels_append]
      simp [halfOpenLabels, hb, List.append_assoc]
    rw [hsplit]
    exact TraceInputDep.sublist (List.sublist_append_right _ _) (.inr ⟨hIO_ab, ih_res⟩)

theorem traceOutputDep_of_outputDep {G : GType} {π ρ : Position}
    (hOut : OutputDep G π ρ) :
    ∀ {d : ℕ} {τ : Position} {l_π l_ρ : Label3},
      ρ = π ++ d :: τ →
      label G π = some l_π →
      label G (π ++ d :: τ) = some l_ρ →
      TraceOutputDep l_π (halfOpenLabels G (π ++ [d]) τ) l_ρ := by
  induction hOut using Relation.TransGen.head_induction_on with
  | @single a hstep =>
    intro d τ l_a l_ρ rfl ha hρ
    have hbase : TraceOutputDep l_a [] l_ρ := by
      rcases hstep with hOO | hIO
      · exact .inl ((isOO_iff ha hρ).mp hOO.2)
      · exact .inr ((isIO_iff ha hρ).mp hIO.2)
    exact TraceOutputDep.sublist (List.nil_sublist _) hbase
  | @head a b hab hbc ih =>
    intro d τ l_a l_ρ rfl ha hρ
    have hprec_ab : Prec G a b := by
      rcases hab with hOO | hIO
      · exact hOO.1
      · exact hIO.1
    rcases prec_to_strict_prefix hprec_ab with ⟨_, hbNode, d₁, τ₁, rfl⟩
    unfold IsNode at hbNode
    rcases Option.isSome_iff_exists.mp hbNode with ⟨l_b, hb⟩
    have hstep_ab : isOO l_a l_b ∨ isIO l_a l_b := by
      rcases hab with hOO | hIO
      · exact .inl ((isOO_iff ha hb).mp hOO.2)
      · exact .inr ((isIO_iff ha hb).mp hIO.2)
    obtain ⟨d₂, τ₂, hρ_eq⟩ := strict_prefix_of_outputDep hbc
    have hρ_eq' : d = d₁ ∧ τ = τ₁ ++ d₂ :: τ₂ := by
      simpa [List.append_assoc] using hρ_eq
    rcases hρ_eq' with ⟨hd, rfl⟩
    subst d
    have hρ' : label G ((a ++ d₁ :: τ₁) ++ d₂ :: τ₂) = some l_ρ := by
      simpa [List.append_assoc] using hρ
    have ih_res := @ih d₂ τ₂ l_b l_ρ (by simp [List.append_assoc]) hb hρ'
    have hsplit :
        halfOpenLabels G (a ++ [d₁]) (τ₁ ++ d₂ :: τ₂) =
          halfOpenLabels G (a ++ [d₁]) τ₁ ++
            (l_b :: halfOpenLabels G ((a ++ d₁ :: τ₁) ++ [d₂]) τ₂) := by
      rw [halfOpenLabels_append]
      simp [halfOpenLabels, hb, List.append_assoc]
    rw [hsplit]
    exact TraceOutputDep.sublist (List.sublist_append_right _ _) (.inr ⟨hstep_ab, ih_res⟩)

theorem prec_of_prefix_append_cons {G : GType} (hG : MuFree G) {π base : Position}
    (hpre : π <+: base) (d : ℕ) (τ : Position)
    (hπ : IsNode G π) (hρ : IsNode G (base ++ d :: τ)) :
    Prec G π (base ++ d :: τ) := by
  rcases hpre with ⟨δ, rfl⟩
  rw [hG.prec_iff]
  refine ⟨hπ, hρ, ?_⟩
  cases δ with
  | nil => exact ⟨d, τ, by simp⟩
  | cons d₀ δ' => exact ⟨d₀, δ' ++ d :: τ, by simp⟩

theorem inputDep_of_traceInputDep {G : GType} (hG : MuFree G) :
    ∀ (τ : Position) {π base : Position} {d : ℕ} {l_π l_ρ : Label3},
      π <+: base →
      label G π = some l_π →
      label G (base ++ d :: τ) = some l_ρ →
      TraceInputDep l_π (halfOpenLabels G (base ++ [d]) τ) l_ρ →
      InputDep G π (base ++ d :: τ)
  | [], π, base, d, l_π, l_ρ, hpre, hπ, hρ, htr => by
    have hπNode : IsNode G π := by unfold IsNode; simp [hπ]
    have hρNode : IsNode G (base ++ [d]) := by unfold IsNode; simp [hρ]
    have hprec : Prec G π (base ++ [d]) :=
      prec_of_prefix_append_cons hG hpre d [] hπNode hρNode
    exact ⟨π, .refl, ⟨hprec, (isII_iff hπ hρ).mpr htr⟩⟩
  | c :: τ, π, base, d, l_π, l_ρ, hpre, hπ, hρ, htr => by
    simp only [halfOpenLabels] at htr
    have hpre' : π <+: base ++ [d] := hpre.trans (List.prefix_append base [d])
    have hρ' : label G ((base ++ [d]) ++ c :: τ) = some l_ρ := by
      simpa [List.append_assoc] using hρ
    cases hlbl : label G (base ++ [d]) with
    | none =>
      rw [hlbl, List.nil_append] at htr
      have res := inputDep_of_traceInputDep hG τ hpre' hπ hρ' htr
      simpa [List.append_assoc] using res
    | some x =>
      rw [hlbl, List.singleton_append] at htr
      rcases htr with hskip | ⟨hIO_step, htake⟩
      · have res := inputDep_of_traceInputDep hG τ hpre' hπ hρ' hskip
        simpa [List.append_assoc] using res
      · have hπNode : IsNode G π := by unfold IsNode; simp [hπ]
        have hxNode : IsNode G (base ++ [d]) := by unfold IsNode; simp [hlbl]
        have hprec : Prec G π (base ++ [d]) :=
          prec_of_prefix_append_cons hG hpre d [] hπNode hxNode
        have hPrecIO : PrecIO G π (base ++ [d]) :=
          ⟨hprec, (isIO_iff hπ hlbl).mpr hIO_step⟩
        obtain ⟨σ, hchain, hII⟩ :=
          inputDep_of_traceInputDep hG τ (List.prefix_refl (base ++ [d])) hlbl hρ' htake
        refine ⟨σ, .head hPrecIO hchain, ?_⟩
        simpa [List.append_assoc] using hII

theorem outputDep_of_traceOutputDep {G : GType} (hG : MuFree G) :
    ∀ (τ : Position) {π base : Position} {d : ℕ} {l_π l_ρ : Label3},
      π <+: base →
      label G π = some l_π →
      label G (base ++ d :: τ) = some l_ρ →
      TraceOutputDep l_π (halfOpenLabels G (base ++ [d]) τ) l_ρ →
      OutputDep G π (base ++ d :: τ)
  | [], π, base, d, l_π, l_ρ, hpre, hπ, hρ, htr => by
    have hπNode : IsNode G π := by unfold IsNode; simp [hπ]
    have hρNode : IsNode G (base ++ [d]) := by unfold IsNode; simp [hρ]
    have hprec : Prec G π (base ++ [d]) :=
      prec_of_prefix_append_cons hG hpre d [] hπNode hρNode
    apply Relation.TransGen.single
    rcases htr with hOO | hIO
    · exact .inl ⟨hprec, (isOO_iff hπ hρ).mpr hOO⟩
    · exact .inr ⟨hprec, (isIO_iff hπ hρ).mpr hIO⟩
  | c :: τ, π, base, d, l_π, l_ρ, hpre, hπ, hρ, htr => by
    simp only [halfOpenLabels] at htr
    have hpre' : π <+: base ++ [d] := hpre.trans (List.prefix_append base [d])
    have hρ' : label G ((base ++ [d]) ++ c :: τ) = some l_ρ := by
      simpa [List.append_assoc] using hρ
    cases hlbl : label G (base ++ [d]) with
    | none =>
      rw [hlbl, List.nil_append] at htr
      have res := outputDep_of_traceOutputDep hG τ hpre' hπ hρ' htr
      simpa [List.append_assoc] using res
    | some x =>
      rw [hlbl, List.singleton_append] at htr
      rcases htr with hskip | ⟨hstep, htake⟩
      · have res := outputDep_of_traceOutputDep hG τ hpre' hπ hρ' hskip
        simpa [List.append_assoc] using res
      · have hπNode : IsNode G π := by unfold IsNode; simp [hπ]
        have hxNode : IsNode G (base ++ [d]) := by unfold IsNode; simp [hlbl]
        have hprec : Prec G π (base ++ [d]) :=
          prec_of_prefix_append_cons hG hpre d [] hπNode hxNode
        have hEdge : PrecOO G π (base ++ [d]) ∨ PrecIO G π (base ++ [d]) := by
          rcases hstep with hOO | hIO
          · exact .inl ⟨hprec, (isOO_iff hπ hlbl).mpr hOO⟩
          · exact .inr ⟨hprec, (isIO_iff hπ hlbl).mpr hIO⟩
        have htail :=
          outputDep_of_traceOutputDep hG τ (List.prefix_refl (base ++ [d])) hlbl hρ' htake
        have res : OutputDep G π ((base ++ [d]) ++ c :: τ) :=
          Relation.TransGen.head hEdge htail
        simpa [List.append_assoc] using res

/-! ### `subterm` and `subst` Position Dichotomy -/

theorem subterm_append (ω σ : Position) :
    ∀ (G : GType), subterm G (ω ++ σ) = (subterm G ω).bind (fun K => subterm K σ) := by
  induction ω with
  | nil => intro G; rfl
  | cons c ω' ih =>
    intro G
    cases G with
    | comm p q k U G' =>
      cases c with
      | zero => exact ih G'
      | succ c => simp [subterm]
    | branch p q k bs =>
      simp only [List.cons_append, subterm]
      cases bs[c]? with
      | none => rfl
      | some b => exact ih b.2
    | par G₁ G₂ =>
      rcases c with _ | _ | c
      · exact ih G₁
      · exact ih G₂
      · simp [subterm]
    | mu t G' =>
      cases c with
      | zero => exact ih G'
      | succ c => simp [subterm]
    | var t => simp [subterm]
    | stop => simp [subterm]

theorem subterm_subst_of_var (t : TVar) (X : GType) (ω σ : Position) :
    ∀ (B : GType), MuFree B → subterm B ω = some (.var t) →
    subterm (MPSTAsync.Linearity.subst t X B) (ω ++ σ) = subterm X σ := by
  induction ω with
  | nil =>
    intro B _ hω
    simp only [subterm, Option.some.injEq] at hω
    subst hω
    simp [MPSTAsync.Linearity.subst]
  | cons c ω' ih =>
    intro B hB hω
    cases hB with
    | comm hG =>
      cases c with
      | zero => exact ih _ hG hω
      | succ c => simp [subterm] at hω
    | branch hbs =>
      rename_i p q k bs
      simp only [subterm] at hω
      cases hbs_c : bs[c]? with
      | none => simp [hbs_c] at hω
      | some b =>
        rcases b with ⟨l, G'⟩
        simp only [hbs_c, Option.bind_some] at hω
        simp only [MPSTAsync.Linearity.subst, List.cons_append, subterm,
          getElem?_substBranches, hbs_c, Option.map_some, Option.bind_some]
        exact ih G' (hbs (l, G') (List.mem_of_getElem? hbs_c)) hω
    | par hG hH =>
      rcases c with _ | _ | c
      · exact ih _ hG hω
      · exact ih _ hH hω
      · simp [subterm] at hω
    | var => simp [subterm] at hω
    | stop => simp [subterm] at hω

theorem label_subst_of_var {t : TVar} {X B : GType} (hB : MuFree B) {ω : Position}
    (hω : subterm B ω = some (.var t)) (σ : Position) :
    label (MPSTAsync.Linearity.subst t X B) (ω ++ σ) = label X σ := by
  unfold label
  rw [subterm_subst_of_var t X ω σ B hB hω]

theorem endKind_subst_of_var {t : TVar} {X B : GType} (hB : MuFree B) {ω : Position}
    (hω : subterm B ω = some (.var t)) (σ : Position) :
    endKind (MPSTAsync.Linearity.subst t X B) (ω ++ σ) = endKind X σ := by
  unfold endKind
  rw [subterm_subst_of_var t X ω σ B hB hω]

theorem halfOpenLabels_subst_of_var {t : TVar} {X B : GType} (hB : MuFree B) {ω : Position}
    (hω : subterm B ω = some (.var t)) (base δ : Position) :
    halfOpenLabels (MPSTAsync.Linearity.subst t X B) (ω ++ base) δ =
      halfOpenLabels X base δ := by
  apply halfOpenLabels_congr
  intro δ' _ _ _
  simpa [List.append_assoc] using label_subst_of_var hB hω (base ++ δ')

theorem subst_pos_dichotomy (t : TVar) (X : GType) (ρ : Position) :
    ∀ (B : GType), MuFree B →
    (∃ ω ρ_X, ρ = ω ++ ρ_X ∧ subterm B ω = some (.var t)) ∨
    (subterm B ρ ≠ some (.var t) ∧
     label (MPSTAsync.Linearity.subst t X B) ρ = label B ρ ∧
     endKind (MPSTAsync.Linearity.subst t X B) ρ = endKind B ρ) := by
  induction ρ with
  | nil =>
    intro B hB
    cases hB with
    | comm _ =>
      exact .inr ⟨by simp [subterm], rfl, rfl⟩
    | branch _ =>
      exact .inr ⟨by simp [subterm], rfl, rfl⟩
    | par _ _ =>
      exact .inr ⟨by simp [subterm], rfl, rfl⟩
    | var =>
      rename_i u
      by_cases htu : t = u
      · subst htu
        exact .inl ⟨[], [], rfl, rfl⟩
      · refine .inr ⟨?_, ?_, ?_⟩
        · simp [subterm, Ne.symm htu]
        · simp [MPSTAsync.Linearity.subst, htu]
        · simp [MPSTAsync.Linearity.subst, htu, endKind, subterm]
    | stop =>
      exact .inr ⟨by simp [subterm], rfl, rfl⟩
  | cons c ρ' ih =>
    intro B hB
    cases hB with
    | comm hG =>
      cases c with
      | zero =>
        rcases ih _ hG with ⟨ω', ρ_X, rfl, hω'⟩ | ⟨hne, hlbl, hek⟩
        · exact .inl ⟨0 :: ω', ρ_X, rfl, hω'⟩
        · exact .inr ⟨hne, hlbl, hek⟩
      | succ c =>
        exact .inr ⟨by simp [subterm], by simp [MPSTAsync.Linearity.subst, label, subterm],
          by simp [MPSTAsync.Linearity.subst, endKind, subterm]⟩
    | branch hbs =>
      rename_i p q k bs
      cases hbs_c : bs[c]? with
      | none =>
        refine .inr ⟨by simp [subterm, hbs_c], ?_, ?_⟩
        · simp [MPSTAsync.Linearity.subst, label, subterm, getElem?_substBranches, hbs_c]
        · simp [MPSTAsync.Linearity.subst, endKind, subterm, getElem?_substBranches, hbs_c]
      | some b =>
        rcases b with ⟨l, G'⟩
        have hG' : MuFree G' := hbs (l, G') (List.mem_of_getElem? hbs_c)
        rcases ih G' hG' with ⟨ω', ρ_X, rfl, hω'⟩ | ⟨hne, hlbl, hek⟩
        · refine .inl ⟨c :: ω', ρ_X, rfl, ?_⟩
          simp [subterm, hbs_c, hω']
        · refine .inr ⟨?_, ?_, ?_⟩
          · simp [subterm, hbs_c, hne]
          · simp only [MPSTAsync.Linearity.subst, label_branch_cons,
              getElem?_substBranches, hbs_c, Option.map_some]
            exact hlbl
          · simp only [MPSTAsync.Linearity.subst, endKind, subterm,
              getElem?_substBranches, hbs_c, Option.map_some, Option.bind_some]
            exact hek
    | par hG hH =>
      rcases c with _ | _ | c
      · rcases ih _ hG with ⟨ω', ρ_X, rfl, hω'⟩ | ⟨hne, hlbl, hek⟩
        · exact .inl ⟨0 :: ω', ρ_X, rfl, hω'⟩
        · exact .inr ⟨hne, hlbl, hek⟩
      · rcases ih _ hH with ⟨ω', ρ_X, rfl, hω'⟩ | ⟨hne, hlbl, hek⟩
        · exact .inl ⟨1 :: ω', ρ_X, rfl, hω'⟩
        · exact .inr ⟨hne, hlbl, hek⟩
      · exact .inr ⟨by simp [subterm], by simp [MPSTAsync.Linearity.subst, label, subterm],
          by simp [MPSTAsync.Linearity.subst, endKind, subterm]⟩
    | var =>
      rename_i u
      by_cases htu : t = u
      · subst htu
        exact .inl ⟨[], c :: ρ', rfl, rfl⟩
      · refine .inr ⟨by simp [subterm], ?_, ?_⟩
        · simp [MPSTAsync.Linearity.subst, htu, label, subterm]
        · simp [MPSTAsync.Linearity.subst, htu, endKind, subterm]
    | stop =>
      refine .inr ⟨by simp [subterm], ?_, ?_⟩
      · simp [MPSTAsync.Linearity.subst, label, subterm]
      · simp [MPSTAsync.Linearity.subst, endKind, subterm]

theorem not_var_prefix_of_subterm_cons_isSome {B : GType} {σ : Position} {d : ℕ} {τ : Position}
    (h : (subterm B (σ ++ d :: τ)).isSome) {ω ρ_X : Position} (hσ : σ = ω ++ ρ_X) {t : TVar}
    (hω : subterm B ω = some (.var t)) : False := by
  subst hσ
  have h1 : subterm B ((ω ++ ρ_X) ++ d :: τ) = none := by
    rw [List.append_assoc, subterm_append, hω]
    cases ρ_X <;> simp [subterm]
  rw [h1] at h
  simp at h

theorem label_subst_of_subterm_cons_isSome {t : TVar} {X B : GType} (hB : MuFree B)
    {σ : Position} {d : ℕ} {τ : Position} (h : (subterm B (σ ++ d :: τ)).isSome) :
    label (MPSTAsync.Linearity.subst t X B) σ = label B σ := by
  rcases subst_pos_dichotomy t X σ B hB with ⟨ω, ρ_X, hσ, hω⟩ | ⟨_, hlbl, _⟩
  · exact False.elim (not_var_prefix_of_subterm_cons_isSome h hσ hω)
  · exact hlbl

theorem halfOpenLabels_subst_of_subterm_isSome {t : TVar} {X B : GType} (hB : MuFree B)
    {base δ : Position} (h : (subterm B (base ++ δ)).isSome) :
    halfOpenLabels (MPSTAsync.Linearity.subst t X B) base δ = halfOpenLabels B base δ := by
  apply halfOpenLabels_congr
  intro δ' d τ hδ
  have h' : (subterm B ((base ++ δ') ++ d :: τ)).isSome := by
    simpa [hδ, List.append_assoc] using h
  exact label_subst_of_subterm_cons_isSome hB h'

theorem endKind_subst_of_not_var_prefix {t : TVar} {X B : GType} (hB : MuFree B)
    {ρ : Position} {ek : EndKind} (h : endKind B ρ = some ek) (hne : ek ≠ .var t) :
    endKind (MPSTAsync.Linearity.subst t X B) ρ = some ek := by
  rcases subst_pos_dichotomy t X ρ B hB with ⟨ω, ρ_X, rfl, hω⟩ | ⟨_, _, hek⟩
  · cases ρ_X with
    | nil =>
      rw [List.append_nil] at h
      have hvar : endKind B ω = some (.var t) := endKind_eq_var_iff.mpr hω
      rw [h] at hvar
      injection hvar with hek_eq
      exact False.elim (hne hek_eq)
    | cons d τ =>
      have hsome : (subterm B (ω ++ d :: τ)).isSome := subterm_isSome_of_endKind_eq_some h
      rw [subterm_append, hω] at hsome
      simp [subterm] at hsome
  · rw [hek, h]

theorem label_subst_of_label_eq_some {t : TVar} {X B : GType} (hB : MuFree B)
    {π : Position} {l : Label3} (h : label B π = some l) :
    label (MPSTAsync.Linearity.subst t X B) π = some l := by
  have hek : endKind B π = some (.node l) := endKind_eq_node_iff.mpr h
  have hek' := endKind_subst_of_not_var_prefix (t := t) (X := X) hB hek (by simp)
  exact endKind_eq_node_iff.mp hek'

/-! ### `RootTrace`, `NodeTrace`, and `TraceSim` -/

def RootTrace (H : GType) (tr : List Label3) (ek : EndKind) : Prop :=
  ∃ ρ, endKind H ρ = some ek ∧ tr = halfOpenLabels H [] ρ

def NodeTrace (H : GType) (l₁ : Label3) (tr : List Label3) (ek : EndKind) : Prop :=
  ∃ π d τ, label H π = some l₁ ∧ endKind H (π ++ d :: τ) = some ek ∧
    tr = halfOpenLabels H (π ++ [d]) τ

def TraceSim (H₁ H₂ : GType) : Prop :=
  (∀ tr ek, RootTrace H₂ tr ek → ∃ tr₁, tr₁ <+ tr ∧ RootTrace H₁ tr₁ ek) ∧
  (∀ l₁ tr ek, NodeTrace H₂ l₁ tr ek → ∃ tr₁, tr₁ <+ tr ∧ NodeTrace H₁ l₁ tr₁ ek)

theorem TraceSim.refl (H : GType) : TraceSim H H :=
  ⟨fun tr _ h => ⟨tr, List.Sublist.refl tr, h⟩,
   fun _ tr _ h => ⟨tr, List.Sublist.refl tr, h⟩⟩

theorem TraceSim.trans {H₁ H₂ H₃ : GType} (h₁₂ : TraceSim H₁ H₂) (h₂₃ : TraceSim H₂ H₃) :
    TraceSim H₁ H₃ := by
  refine ⟨?_, ?_⟩
  · intro tr ek h₃
    obtain ⟨tr₂, hsub₂, h₂⟩ := h₂₃.1 tr ek h₃
    obtain ⟨tr₁, hsub₁, h₁⟩ := h₁₂.1 tr₂ ek h₂
    exact ⟨tr₁, hsub₁.trans hsub₂, h₁⟩
  · intro l₁ tr ek h₃
    obtain ⟨tr₂, hsub₂, h₂⟩ := h₂₃.2 l₁ tr ek h₃
    obtain ⟨tr₁, hsub₁, h₁⟩ := h₁₂.2 l₁ tr₂ ek h₂
    exact ⟨tr₁, hsub₁.trans hsub₂, h₁⟩

theorem rootTrace_of_subst {t : TVar} {X B : GType} (hB : MuFree B) {tr : List Label3} {ek : EndKind}
    (h : RootTrace (MPSTAsync.Linearity.subst t X B) tr ek) :
    (RootTrace B tr ek ∧ ek ≠ .var t) ∨
    ∃ tr_B tr_X, tr = tr_B ++ tr_X ∧ RootTrace B tr_B (.var t) ∧ RootTrace X tr_X ek := by
  rcases h with ⟨ρ, hek, rfl⟩
  rcases subst_pos_dichotomy t X ρ B hB with ⟨ω, ρ_X, rfl, hω⟩ | ⟨hne_var, _, hek_eq⟩
  · right
    refine ⟨halfOpenLabels B [] ω, halfOpenLabels X [] ρ_X, ?_, ?_, ?_⟩
    · rw [halfOpenLabels_append]
      have hω_some : (subterm B ([] ++ ω)).isSome := by simp [hω]
      rw [halfOpenLabels_subst_of_subterm_isSome hB hω_some]
      have hX_part := halfOpenLabels_subst_of_var (X := X) hB hω [] ρ_X
      simpa using congrArg (halfOpenLabels B [] ω ++ ·) hX_part
    · exact ⟨ω, endKind_eq_var_iff.mpr hω, rfl⟩
    · rw [endKind_subst_of_var hB hω] at hek
      exact ⟨ρ_X, hek, rfl⟩
  · left
    rw [hek_eq] at hek
    have hne : ek ≠ .var t := by
      rintro rfl
      exact hne_var (endKind_eq_var_iff.mp hek)
    have hsome : (subterm B ([] ++ ρ)).isSome := subterm_isSome_of_endKind_eq_some hek
    rw [halfOpenLabels_subst_of_subterm_isSome hB hsome]
    exact ⟨⟨ρ, hek, rfl⟩, hne⟩

theorem rootTrace_subst_left {t : TVar} {X B : GType} (hB : MuFree B) {tr : List Label3} {ek : EndKind}
    (h : RootTrace B tr ek) (hne : ek ≠ .var t) :
    RootTrace (MPSTAsync.Linearity.subst t X B) tr ek := by
  rcases h with ⟨ρ, hek, rfl⟩
  have hsome : (subterm B ([] ++ ρ)).isSome := subterm_isSome_of_endKind_eq_some hek
  refine ⟨ρ, endKind_subst_of_not_var_prefix hB hek hne, ?_⟩
  rw [halfOpenLabels_subst_of_subterm_isSome hB hsome]

theorem rootTrace_subst_splice {t : TVar} {X B : GType} (hB : MuFree B)
    {tr_B tr_X : List Label3} {ek : EndKind}
    (h₁ : RootTrace B tr_B (.var t)) (h₂ : RootTrace X tr_X ek) :
    RootTrace (MPSTAsync.Linearity.subst t X B) (tr_B ++ tr_X) ek := by
  rcases h₁ with ⟨ω, hω_ek, rfl⟩
  rcases h₂ with ⟨ρ_X, hρ_X, rfl⟩
  have hω : subterm B ω = some (.var t) := endKind_eq_var_iff.mp hω_ek
  refine ⟨ω ++ ρ_X, ?_, ?_⟩
  · rw [endKind_subst_of_var hB hω]; exact hρ_X
  · rw [halfOpenLabels_append]
    have hω_some : (subterm B ([] ++ ω)).isSome := by simp [hω]
    rw [halfOpenLabels_subst_of_subterm_isSome hB hω_some]
    have hX_part := halfOpenLabels_subst_of_var (X := X) hB hω [] ρ_X
    simpa using congrArg (halfOpenLabels B [] ω ++ ·) hX_part.symm

theorem append_cons_eq_append {α : Type*} :
    ∀ (π : List α) (d : α) (τ ω ρ_X : List α),
      π ++ d :: τ = ω ++ ρ_X →
      ω <+: π ∨ ∃ τ_B, ω = π ++ d :: τ_B ∧ τ = τ_B ++ ρ_X
  | [], _, _, [], _, _ => .inl List.nil_prefix
  | [], _, _, _ :: ω', _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, hτ⟩
    exact .inr ⟨ω', rfl, hτ⟩
  | _ :: _, _, _, [], _, _ => .inl List.nil_prefix
  | _ :: π', d, τ, _ :: ω', ρ_X, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, h'⟩
    rcases append_cons_eq_append π' d τ ω' ρ_X h' with ⟨δ, rfl⟩ | ⟨τ_B, rfl, rfl⟩
    · exact .inl ⟨δ, rfl⟩
    · exact .inr ⟨τ_B, rfl, rfl⟩

theorem nodeTrace_of_subst {t : TVar} {X B : GType} (hB : MuFree B)
    {l₁ : Label3} {tr : List Label3} {ek : EndKind}
    (h : NodeTrace (MPSTAsync.Linearity.subst t X B) l₁ tr ek) :
    (NodeTrace B l₁ tr ek ∧ ek ≠ .var t) ∨
    ((∃ tr_B, RootTrace B tr_B (.var t)) ∧ NodeTrace X l₁ tr ek) ∨
    ∃ tr_B tr_X, tr = tr_B ++ tr_X ∧ NodeTrace B l₁ tr_B (.var t) ∧ RootTrace X tr_X ek := by
  rcases h with ⟨π, d, τ, hπ, hek, rfl⟩
  rcases subst_pos_dichotomy t X π B hB with ⟨ω, π_X, rfl, hω⟩ | ⟨_, hlbl_π, _⟩
  · right; left
    refine ⟨⟨halfOpenLabels B [] ω, ω, endKind_eq_var_iff.mpr hω, rfl⟩, π_X, d, τ, ?_, ?_, ?_⟩
    · rw [label_subst_of_var hB hω] at hπ; exact hπ
    · have hek' : endKind (MPSTAsync.Linearity.subst t X B) (ω ++ (π_X ++ d :: τ)) = some ek := by
        simpa [List.append_assoc] using hek
      rw [endKind_subst_of_var hB hω] at hek'
      exact hek'
    · simpa [List.append_assoc] using halfOpenLabels_subst_of_var hB hω (π_X ++ [d]) τ
  · rw [hlbl_π] at hπ
    rcases subst_pos_dichotomy t X (π ++ d :: τ) B hB with
      ⟨ω, ρ_X, h_eq, hω⟩ | ⟨hne_var, _, hek_eq⟩
    · rcases append_cons_eq_append π d τ ω ρ_X h_eq with ⟨σ, rfl⟩ | ⟨τ_B, rfl, rfl⟩
      · have hbad : label B (ω ++ σ) = none := by
          unfold label
          rw [subterm_append, hω]
          cases σ <;> simp [subterm]
        rw [hbad] at hπ
        simp at hπ
      · right; right
        refine ⟨halfOpenLabels B (π ++ [d]) τ_B, halfOpenLabels X [] ρ_X, ?_, ?_, ?_⟩
        · rw [halfOpenLabels_append]
          have hω_some : (subterm B ((π ++ [d]) ++ τ_B)).isSome := by
            simpa [List.append_assoc] using (by simp [hω] : (subterm B (π ++ d :: τ_B)).isSome)
          rw [halfOpenLabels_subst_of_subterm_isSome hB hω_some]
          have hX_part := halfOpenLabels_subst_of_var (X := X) hB hω [] ρ_X
          have hX_part' :
              halfOpenLabels (MPSTAsync.Linearity.subst t X B) ((π ++ [d]) ++ τ_B) ρ_X =
                halfOpenLabels X [] ρ_X := by
            simpa [List.append_assoc] using hX_part
          rw [hX_part']
        · exact ⟨π, d, τ_B, hπ, endKind_eq_var_iff.mpr hω, rfl⟩
        · have hek' : endKind (MPSTAsync.Linearity.subst t X B) ((π ++ d :: τ_B) ++ ρ_X) = some ek := by
            simpa [List.append_assoc] using hek
          rw [endKind_subst_of_var hB hω] at hek'
          exact ⟨ρ_X, hek', rfl⟩
    · left
      rw [hek_eq] at hek
      have hne : ek ≠ .var t := by
        rintro rfl
        exact hne_var (endKind_eq_var_iff.mp hek)
      have hsome : (subterm B ((π ++ [d]) ++ τ)).isSome := by
        simpa [List.append_assoc] using subterm_isSome_of_endKind_eq_some hek
      rw [halfOpenLabels_subst_of_subterm_isSome hB hsome]
      exact ⟨⟨π, d, τ, hπ, hek, rfl⟩, hne⟩

theorem nodeTrace_subst_left {t : TVar} {X B : GType} (hB : MuFree B)
    {l₁ : Label3} {tr : List Label3} {ek : EndKind}
    (h : NodeTrace B l₁ tr ek) (hne : ek ≠ .var t) :
    NodeTrace (MPSTAsync.Linearity.subst t X B) l₁ tr ek := by
  rcases h with ⟨π, d, τ, hπ, hek, rfl⟩
  have hsome : (subterm B ((π ++ [d]) ++ τ)).isSome := by
    simpa [List.append_assoc] using subterm_isSome_of_endKind_eq_some hek
  refine ⟨π, d, τ, label_subst_of_label_eq_some hB hπ,
    endKind_subst_of_not_var_prefix hB hek hne, ?_⟩
  rw [halfOpenLabels_subst_of_subterm_isSome hB hsome]

theorem nodeTrace_subst_right {t : TVar} {X B : GType} (hB : MuFree B)
    {tr_B : List Label3} {l₁ : Label3} {tr : List Label3} {ek : EndKind}
    (h₁ : RootTrace B tr_B (.var t)) (h₂ : NodeTrace X l₁ tr ek) :
    NodeTrace (MPSTAsync.Linearity.subst t X B) l₁ tr ek := by
  rcases h₁ with ⟨ω, hω_ek, _⟩
  rcases h₂ with ⟨π_X, d, τ, hπ_X, hek_X, rfl⟩
  have hω : subterm B ω = some (.var t) := endKind_eq_var_iff.mp hω_ek
  refine ⟨ω ++ π_X, d, τ, ?_, ?_, ?_⟩
  · rw [label_subst_of_var hB hω]; exact hπ_X
  · have h_eq : (ω ++ π_X) ++ d :: τ = ω ++ (π_X ++ d :: τ) := by simp [List.append_assoc]
    rw [h_eq, endKind_subst_of_var hB hω]; exact hek_X
  · have h_eq : (ω ++ π_X) ++ [d] = ω ++ (π_X ++ [d]) := by simp [List.append_assoc]
    rw [h_eq, halfOpenLabels_subst_of_var hB hω]

theorem nodeTrace_subst_splice {t : TVar} {X B : GType} (hB : MuFree B)
    {l₁ : Label3} {tr_B tr_X : List Label3} {ek : EndKind}
    (h₁ : NodeTrace B l₁ tr_B (.var t)) (h₂ : RootTrace X tr_X ek) :
    NodeTrace (MPSTAsync.Linearity.subst t X B) l₁ (tr_B ++ tr_X) ek := by
  rcases h₁ with ⟨π, d, τ_B, hπ, hω_ek, rfl⟩
  rcases h₂ with ⟨ρ_X, hρ_X, rfl⟩
  have hω : subterm B (π ++ d :: τ_B) = some (.var t) := endKind_eq_var_iff.mp hω_ek
  refine ⟨π, d, τ_B ++ ρ_X, label_subst_of_label_eq_some hB hπ, ?_, ?_⟩
  · have h_eq : π ++ d :: (τ_B ++ ρ_X) = (π ++ d :: τ_B) ++ ρ_X := by simp [List.append_assoc]
    rw [h_eq, endKind_subst_of_var hB hω]; exact hρ_X
  · rw [halfOpenLabels_append]
    have hω_some : (subterm B ((π ++ [d]) ++ τ_B)).isSome := by
      simpa [List.append_assoc] using (by simp [hω] : (subterm B (π ++ d :: τ_B)).isSome)
    rw [halfOpenLabels_subst_of_subterm_isSome hB hω_some]
    have hX_part := halfOpenLabels_subst_of_var (X := X) hB hω [] ρ_X
    have hX_part' :
        halfOpenLabels (MPSTAsync.Linearity.subst t X B) ((π ++ [d]) ++ τ_B) ρ_X =
          halfOpenLabels X [] ρ_X := by
      simpa [List.append_assoc] using hX_part
    rw [hX_part']

theorem TraceSim.subst {t : TVar} {X₁ X₂ B₁ B₂ : GType}
    (hB₁ : MuFree B₁) (hB₂ : MuFree B₂)
    (hX : TraceSim X₁ X₂) (hB : TraceSim B₁ B₂) :
    TraceSim (MPSTAsync.Linearity.subst t X₁ B₁) (MPSTAsync.Linearity.subst t X₂ B₂) := by
  refine ⟨?_, ?_⟩
  · intro tr ek h
    rcases rootTrace_of_subst hB₂ h with ⟨hB₂_tr, hne⟩ | ⟨tr_B, tr_X, rfl, hB₂_tr, hX₂_tr⟩
    · obtain ⟨tr₁, hsub, hB₁_tr⟩ := hB.1 tr ek hB₂_tr
      exact ⟨tr₁, hsub, rootTrace_subst_left hB₁ hB₁_tr hne⟩
    · obtain ⟨tr_B₁, hsub_B, hB₁_tr⟩ := hB.1 tr_B (.var t) hB₂_tr
      obtain ⟨tr_X₁, hsub_X, hX₁_tr⟩ := hX.1 tr_X ek hX₂_tr
      exact ⟨tr_B₁ ++ tr_X₁, hsub_B.append hsub_X, rootTrace_subst_splice hB₁ hB₁_tr hX₁_tr⟩
  · intro l₁ tr ek h
    rcases nodeTrace_of_subst hB₂ h with
      ⟨hB₂_tr, hne⟩ | ⟨⟨tr_B, hB₂_var⟩, hX₂_tr⟩ | ⟨tr_B, tr_X, rfl, hB₂_tr, hX₂_tr⟩
    · obtain ⟨tr₁, hsub, hB₁_tr⟩ := hB.2 l₁ tr ek hB₂_tr
      exact ⟨tr₁, hsub, nodeTrace_subst_left hB₁ hB₁_tr hne⟩
    · obtain ⟨tr_B₁, _, hB₁_var⟩ := hB.1 tr_B (.var t) hB₂_var
      obtain ⟨tr₁, hsub, hX₁_tr⟩ := hX.2 l₁ tr ek hX₂_tr
      exact ⟨tr₁, hsub, nodeTrace_subst_right hB₁ hB₁_var hX₁_tr⟩
    · obtain ⟨tr_B₁, hsub_B, hB₁_tr⟩ := hB.2 l₁ tr_B (.var t) hB₂_tr
      obtain ⟨tr_X₁, hsub_X, hX₁_tr⟩ := hX.1 tr_X ek hX₂_tr
      exact ⟨tr_B₁ ++ tr_X₁, hsub_B.append hsub_X, nodeTrace_subst_splice hB₁ hB₁_tr hX₁_tr⟩

theorem TraceSim.iter_subst_congr {t : TVar} {B₁ B₂ : GType}
    (hB₁ : MuFree B₁) (hB₂ : MuFree B₂) (hB : TraceSim B₁ B₂) :
    ∀ m, TraceSim ((fun X => MPSTAsync.Linearity.subst t X B₁)^[m] .stop)
                  ((fun X => MPSTAsync.Linearity.subst t X B₂)^[m] .stop)
  | 0 => TraceSim.refl .stop
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact TraceSim.subst hB₁ hB₂ (TraceSim.iter_subst_congr hB₁ hB₂ hB m) hB

theorem not_rootTrace_stop {tr : List Label3} {ek : EndKind} :
    ¬ RootTrace .stop tr ek := by
  rintro ⟨ρ, hek, _⟩
  cases ρ <;> simp [endKind, subterm] at hek

theorem not_nodeTrace_stop {l₁ : Label3} {tr : List Label3} {ek : EndKind} :
    ¬ NodeTrace .stop l₁ tr ek := by
  rintro ⟨π, _, _, hπ, _, _⟩
  simp at hπ

theorem rootTrace_of_iter_subst {t : TVar} {B : GType} (hB : MuFree B) :
    ∀ (m : ℕ) {tr : List Label3} {ek : EndKind},
      RootTrace ((fun X => MPSTAsync.Linearity.subst t X B)^[m] .stop) tr ek →
      ∃ tr₀, tr₀ <+ tr ∧ RootTrace B tr₀ ek ∧ ek ≠ .var t
  | 0, _, _, h => False.elim (not_rootTrace_stop h)
  | m + 1, tr, ek, h => by
    rw [Function.iterate_succ_apply'] at h
    rcases rootTrace_of_subst hB h with ⟨hB_tr, hne⟩ | ⟨tr_B, tr_X, rfl, _, hX_tr⟩
    · exact ⟨tr, List.Sublist.refl tr, hB_tr, hne⟩
    · obtain ⟨tr₀, hsub, hB_tr, hne⟩ := rootTrace_of_iter_subst hB m hX_tr
      exact ⟨tr₀, hsub.trans (List.sublist_append_right tr_B tr_X), hB_tr, hne⟩

theorem nodeTrace_of_iter_subst {t : TVar} {B : GType} (hB : MuFree B) :
    ∀ (m : ℕ) {l₁ : Label3} {tr : List Label3} {ek : EndKind},
      NodeTrace ((fun X => MPSTAsync.Linearity.subst t X B)^[m] .stop) l₁ tr ek →
      ∃ tr₁, tr₁ <+ tr ∧
        NodeTrace ((fun X => MPSTAsync.Linearity.subst t X B)^[2] .stop) l₁ tr₁ ek
  | 0, _, _, _, h => False.elim (not_nodeTrace_stop h)
  | m + 1, l₁, tr, ek, h => by
    rw [Function.iterate_succ_apply'] at h
    have hF2_eq :
        ((fun X => MPSTAsync.Linearity.subst t X B)^[2] .stop) =
          MPSTAsync.Linearity.subst t (MPSTAsync.Linearity.subst t .stop B) B := rfl
    rcases nodeTrace_of_subst hB h with
      ⟨hB_tr, hne⟩ | ⟨_, hX_tr⟩ | ⟨tr_B, tr_X, rfl, hB_tr, hX_tr⟩
    · refine ⟨tr, List.Sublist.refl tr, ?_⟩
      rw [hF2_eq]
      exact nodeTrace_subst_left hB hB_tr hne
    · exact nodeTrace_of_iter_subst hB m hX_tr
    · obtain ⟨tr₀, hsub, hB_root, hne⟩ := rootTrace_of_iter_subst hB m hX_tr
      have hF1_root : RootTrace (MPSTAsync.Linearity.subst t .stop B) tr₀ ek :=
        rootTrace_subst_left hB hB_root hne
      refine ⟨tr_B ++ tr₀, (List.Sublist.refl tr_B).append hsub, ?_⟩
      rw [hF2_eq]
      exact nodeTrace_subst_splice hB hB_tr hF1_root

theorem TraceSim.iter_subst_two_of_succ {t : TVar} {B : GType} (hB : MuFree B) (m : ℕ) :
    TraceSim ((fun X => MPSTAsync.Linearity.subst t X B)^[2] .stop)
             ((fun X => MPSTAsync.Linearity.subst t X B)^[m] .stop) := by
  refine ⟨?_, ?_⟩
  · intro tr ek h
    obtain ⟨tr₀, hsub, hB_tr, hne⟩ := rootTrace_of_iter_subst hB m h
    have hF2_eq :
        ((fun X => MPSTAsync.Linearity.subst t X B)^[2] .stop) =
          MPSTAsync.Linearity.subst t (MPSTAsync.Linearity.subst t .stop B) B := rfl
    refine ⟨tr₀, hsub, ?_⟩
    rw [hF2_eq]
    exact rootTrace_subst_left hB hB_tr hne
  · intro l₁ tr ek h
    exact nodeTrace_of_iter_subst hB m h

theorem halfOpenLabels_comm_zero (p q : Role) (k : ℕ) (U : VType) (G : GType) (base δ : Position) :
    halfOpenLabels (.comm p q k U G) (0 :: base) δ = halfOpenLabels G base δ := by
  apply halfOpenLabels_congr
  intro _ _ _ _
  rfl

theorem halfOpenLabels_branch_cons (p q : Role) (k : ℕ) (bs : List (Label × GType))
    (i : ℕ) (l : Label) (G : GType) (hbs : bs[i]? = some (l, G)) (base δ : Position) :
    halfOpenLabels (.branch p q k bs) (i :: base) δ = halfOpenLabels G base δ := by
  apply halfOpenLabels_congr
  intro δ' _ _ _
  simp only [List.cons_append, label_branch_cons, hbs]

theorem halfOpenLabels_par_zero (G H : GType) (base δ : Position) :
    halfOpenLabels (.par G H) (0 :: base) δ = halfOpenLabels G base δ := by
  apply halfOpenLabels_congr
  intro _ _ _ _
  rfl

theorem halfOpenLabels_par_one (G H : GType) (base δ : Position) :
    halfOpenLabels (.par G H) (1 :: base) δ = halfOpenLabels H base δ := by
  apply halfOpenLabels_congr
  intro _ _ _ _
  rfl

theorem TraceSim.comm (p q : Role) (k : ℕ) (U : VType) {G₁ G₂ : GType}
    (hG : TraceSim G₁ G₂) :
    TraceSim (.comm p q k U G₁) (.comm p q k U G₂) := by
  refine ⟨?_, ?_⟩
  · rintro tr ek ⟨ρ, hek, rfl⟩
    cases ρ with
    | nil =>
      simp only [endKind, subterm, Option.some.injEq] at hek
      subst hek
      exact ⟨[], List.Sublist.refl [], [], rfl, rfl⟩
    | cons c ρ' =>
      cases c with
      | zero =>
        simp only [endKind, subterm] at hek
        simp only [halfOpenLabels, List.nil_append, label_comm_nil, List.singleton_append]
        rw [halfOpenLabels_comm_zero]
        obtain ⟨tr₁, hsub, ρ₁', hek₁, htr₁⟩ := hG.1 (halfOpenLabels G₂ [] ρ') ek ⟨ρ', hek, rfl⟩
        refine ⟨(p, q, k) :: tr₁, hsub.cons_cons _, 0 :: ρ₁', hek₁, ?_⟩
        simp [halfOpenLabels, halfOpenLabels_comm_zero, htr₁]
      | succ c =>
        simp [endKind, subterm] at hek
  · rintro l₁ tr ek ⟨π, d, τ, hπ, hek, rfl⟩
    cases π with
    | nil =>
      simp only [label_comm_nil, Option.some.injEq] at hπ
      subst hπ
      cases d with
      | zero =>
        simp only [List.nil_append, endKind, subterm] at hek
        rw [List.nil_append, halfOpenLabels_comm_zero]
        obtain ⟨tr₁, hsub, ρ₁, hek₁, htr₁⟩ := hG.1 (halfOpenLabels G₂ [] τ) ek ⟨τ, hek, rfl⟩
        refine ⟨tr₁, hsub, [], 0, ρ₁, rfl, hek₁, ?_⟩
        simp [halfOpenLabels_comm_zero, htr₁]
      | succ d =>
        simp [endKind, subterm] at hek
    | cons c π' =>
      cases c with
      | zero =>
        simp only [label_comm_zero] at hπ
        simp only [List.cons_append, endKind, subterm] at hek
        simp only [List.cons_append]
        rw [halfOpenLabels_comm_zero]
        obtain ⟨tr₁, hsub, π₁', d₁, τ₁, hπ₁, hek₁, htr₁⟩ :=
          hG.2 l₁ (halfOpenLabels G₂ (π' ++ [d]) τ) ek ⟨π', d, τ, hπ, hek, rfl⟩
        refine ⟨tr₁, hsub, 0 :: π₁', d₁, τ₁, hπ₁, hek₁, ?_⟩
        simp [halfOpenLabels_comm_zero, htr₁]
      | succ c =>
        unfold label subterm at hπ; simp at hπ

theorem TraceSim.branch (p q : Role) (k : ℕ) {bs₁ bs₂ : List (Label × GType)}
    (hbs : ∀ (i : ℕ) (l₂ : Label) (G₂ : GType), bs₂[i]? = some (l₂, G₂) →
      ∃ l₁ G₁, bs₁[i]? = some (l₁, G₁) ∧ TraceSim G₁ G₂) :
    TraceSim (.branch p q k bs₁) (.branch p q k bs₂) := by
  refine ⟨?_, ?_⟩
  · rintro tr ek ⟨ρ, hek, rfl⟩
    cases ρ with
    | nil =>
      simp only [endKind, subterm, Option.some.injEq] at hek
      subst hek
      exact ⟨[], List.Sublist.refl [], [], rfl, rfl⟩
    | cons i ρ' =>
      simp only [endKind, subterm] at hek
      cases hbs₂ : bs₂[i]? with
      | none => simp [hbs₂] at hek
      | some b₂ =>
        rcases b₂ with ⟨l₂, G₂⟩
        simp only [hbs₂, Option.bind_some] at hek
        obtain ⟨l₁, G₁, hbs₁, hsim⟩ := hbs i l₂ G₂ hbs₂
        simp only [halfOpenLabels, List.nil_append, label_branch_nil, List.singleton_append]
        rw [halfOpenLabels_branch_cons p q k bs₂ i l₂ G₂ hbs₂]
        obtain ⟨tr₁, hsub, ρ₁', hek₁, htr₁⟩ :=
          hsim.1 (halfOpenLabels G₂ [] ρ') ek ⟨ρ', hek, rfl⟩
        refine ⟨(p, q, k) :: tr₁, hsub.cons_cons _, i :: ρ₁', ?_, ?_⟩
        · simp [endKind, subterm, hbs₁]; exact hek₁
        · simp [halfOpenLabels, halfOpenLabels_branch_cons p q k bs₁ i l₁ G₁ hbs₁, htr₁]
  · rintro l₁ tr ek ⟨π, d, τ, hπ, hek, rfl⟩
    cases π with
    | nil =>
      simp only [label_branch_nil, Option.some.injEq] at hπ
      subst hπ
      simp only [List.nil_append, endKind, subterm] at hek
      cases hbs₂ : bs₂[d]? with
      | none => simp [hbs₂] at hek
      | some b₂ =>
        rcases b₂ with ⟨lbl₂, G₂⟩
        simp only [hbs₂, Option.bind_some] at hek
        obtain ⟨lbl₁, G₁, hbs₁, hsim⟩ := hbs d lbl₂ G₂ hbs₂
        rw [List.nil_append, halfOpenLabels_branch_cons p q k bs₂ d lbl₂ G₂ hbs₂]
        obtain ⟨tr₁, hsub, ρ₁, hek₁, htr₁⟩ :=
          hsim.1 (halfOpenLabels G₂ [] τ) ek ⟨τ, hek, rfl⟩
        refine ⟨tr₁, hsub, [], d, ρ₁, rfl, ?_, ?_⟩
        · simp [endKind, subterm, hbs₁]; exact hek₁
        · simp [halfOpenLabels_branch_cons p q k bs₁ d lbl₁ G₁ hbs₁, htr₁]
    | cons i π' =>
      rw [label_branch_cons] at hπ
      cases hbs₂ : bs₂[i]? with
      | none => simp [hbs₂] at hπ
      | some b₂ =>
        rcases b₂ with ⟨lbl₂, G₂⟩
        simp only [hbs₂] at hπ
        simp only [List.cons_append, endKind, subterm, hbs₂, Option.bind_some] at hek
        obtain ⟨lbl₁, G₁, hbs₁, hsim⟩ := hbs i lbl₂ G₂ hbs₂
        simp only [List.cons_append]
        rw [halfOpenLabels_branch_cons p q k bs₂ i lbl₂ G₂ hbs₂]
        obtain ⟨tr₁, hsub, π₁', d₁, τ₁, hπ₁, hek₁, htr₁⟩ :=
          hsim.2 l₁ (halfOpenLabels G₂ (π' ++ [d]) τ) ek ⟨π', d, τ, hπ, hek, rfl⟩
        refine ⟨tr₁, hsub, i :: π₁', d₁, τ₁, ?_, ?_, ?_⟩
        · rw [label_branch_cons, hbs₁]; exact hπ₁
        · simp [endKind, subterm, hbs₁]; exact hek₁
        · simp [halfOpenLabels_branch_cons p q k bs₁ i lbl₁ G₁ hbs₁, htr₁]

theorem TraceSim.par {G₁ G₂ H₁ H₂ : GType}
    (hG : TraceSim G₁ G₂) (hH : TraceSim H₁ H₂) :
    TraceSim (.par G₁ H₁) (.par G₂ H₂) := by
  refine ⟨?_, ?_⟩
  · rintro tr ek ⟨ρ, hek, rfl⟩
    cases ρ with
    | nil => simp [endKind, subterm] at hek
    | cons c ρ' =>
      match c with
      | 0 =>
        simp only [endKind, subterm] at hek
        simp only [halfOpenLabels, label_par_nil, List.nil_append]
        rw [halfOpenLabels_par_zero]
        obtain ⟨tr₁, hsub, ρ₁', hek₁, htr₁⟩ := hG.1 (halfOpenLabels G₂ [] ρ') ek ⟨ρ', hek, rfl⟩
        refine ⟨tr₁, hsub, 0 :: ρ₁', hek₁, ?_⟩
        simp [halfOpenLabels, halfOpenLabels_par_zero, htr₁]
      | 1 =>
        simp only [endKind, subterm] at hek
        simp only [halfOpenLabels, label_par_nil, List.nil_append]
        rw [halfOpenLabels_par_one]
        obtain ⟨tr₁, hsub, ρ₁', hek₁, htr₁⟩ := hH.1 (halfOpenLabels H₂ [] ρ') ek ⟨ρ', hek, rfl⟩
        refine ⟨tr₁, hsub, 1 :: ρ₁', hek₁, ?_⟩
        simp [halfOpenLabels, halfOpenLabels_par_one, htr₁]
      | c + 2 =>
        simp [endKind, subterm] at hek
  · rintro l₁ tr ek ⟨π, d, τ, hπ, hek, rfl⟩
    cases π with
    | nil => simp at hπ
    | cons c π' =>
      match c with
      | 0 =>
        simp only [label_par_zero] at hπ
        simp only [List.cons_append, endKind, subterm] at hek
        simp only [List.cons_append]
        rw [halfOpenLabels_par_zero]
        obtain ⟨tr₁, hsub, π₁', d₁, τ₁, hπ₁, hek₁, htr₁⟩ :=
          hG.2 l₁ (halfOpenLabels G₂ (π' ++ [d]) τ) ek ⟨π', d, τ, hπ, hek, rfl⟩
        refine ⟨tr₁, hsub, 0 :: π₁', d₁, τ₁, hπ₁, hek₁, ?_⟩
        simp [halfOpenLabels_par_zero, htr₁]
      | 1 =>
        simp only [label_par_one] at hπ
        simp only [List.cons_append, endKind, subterm] at hek
        simp only [List.cons_append]
        rw [halfOpenLabels_par_one]
        obtain ⟨tr₁, hsub, π₁', d₁, τ₁, hπ₁, hek₁, htr₁⟩ :=
          hH.2 l₁ (halfOpenLabels H₂ (π' ++ [d]) τ) ek ⟨π', d, τ, hπ, hek, rfl⟩
        refine ⟨tr₁, hsub, 1 :: π₁', d₁, τ₁, hπ₁, hek₁, ?_⟩
        simp [halfOpenLabels_par_one, htr₁]
      | c + 2 =>
        unfold label subterm at hπ; simp at hπ

mutual
  theorem traceSim_unfold (n : ℕ) :
      (G : GType) → TraceSim (MPSTAsync.Linearity.unfold 1 G) (MPSTAsync.Linearity.unfold n G)
    | .comm p q k U G => TraceSim.comm p q k U (traceSim_unfold n G)
    | .branch p q k bs => by
      apply TraceSim.branch p q k
      intro i l₂ G₂ hbs₂
      rw [getElem?_unfoldBranches] at hbs₂
      cases hbs : bs[i]? with
      | none => simp [hbs] at hbs₂
      | some b =>
        rcases b with ⟨l, G⟩
        simp only [hbs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hbs₂
        rcases hbs₂ with ⟨rfl, rfl⟩
        refine ⟨l, MPSTAsync.Linearity.unfold 1 G, ?_, traceSim_unfoldBranches n bs i l G hbs⟩
        rw [getElem?_unfoldBranches, hbs]
        rfl
    | .par G H => TraceSim.par (traceSim_unfold n G) (traceSim_unfold n H)
    | .mu t G => by
      unfold MPSTAsync.Linearity.unfold
      have hB₁ : MuFree (MPSTAsync.Linearity.unfold 1 G) := MuFree.unfold 1 G
      have hB₂ : MuFree (MPSTAsync.Linearity.unfold n G) := MuFree.unfold n G
      have hsimB : TraceSim (MPSTAsync.Linearity.unfold 1 G) (MPSTAsync.Linearity.unfold n G) :=
        traceSim_unfold n G
      exact (TraceSim.iter_subst_two_of_succ hB₁ (n + 1)).trans
        (TraceSim.iter_subst_congr hB₁ hB₂ hsimB (n + 1))
    | .var _ => TraceSim.refl _
    | .stop => TraceSim.refl _

  theorem traceSim_unfoldBranches (n : ℕ) :
      (bs : List (Label × GType)) →
      ∀ (i : ℕ) (l : Label) (G : GType), bs[i]? = some (l, G) →
      TraceSim (MPSTAsync.Linearity.unfold 1 G) (MPSTAsync.Linearity.unfold n G)
    | [], i, _, _, hbs => by simp at hbs
    | (_, G₀) :: bs, 0, _, G, hbs => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hbs
      rcases hbs with ⟨_, rfl⟩
      exact traceSim_unfold n G₀
    | _ :: bs, i + 1, l, G, hbs => by
      simp only [List.getElem?_cons_succ] at hbs
      exact traceSim_unfoldBranches n bs i l G hbs
end

theorem TraceSim.mainLinear {H₁ H₂ : GType} (hsim : TraceSim H₁ H₂)
    (h₁ : MuFree H₁) (h₂ : MuFree H₂) (hlin : MainLinear H₁) :
    MainLinear H₂ := by
  intro π ρ p₁ q₁ p₂ q₂ k hprec hlblπ hlblρ
  rcases prec_to_strict_prefix hprec with ⟨_, _, d, τ, rfl⟩
  have hNode₂ : NodeTrace H₂ (p₁, q₁, k) (halfOpenLabels H₂ (π ++ [d]) τ) (.node (p₂, q₂, k)) :=
    ⟨π, d, τ, hlblπ, endKind_eq_node_iff.mpr hlblρ, rfl⟩
  obtain ⟨tr₁, hsub, π₁, d₁, τ₁, hlblπ₁, hekρ₁, rfl⟩ := hsim.2 _ _ _ hNode₂
  have hlblρ₁ : label H₁ (π₁ ++ d₁ :: τ₁) = some (p₂, q₂, k) :=
    endKind_eq_node_iff.mp hekρ₁
  have hπ₁Node : IsNode H₁ π₁ := by unfold IsNode; simp [hlblπ₁]
  have hρ₁Node : IsNode H₁ (π₁ ++ d₁ :: τ₁) := by unfold IsNode; simp [hlblρ₁]
  have hprec₁ : Prec H₁ π₁ (π₁ ++ d₁ :: τ₁) :=
    (h₁.prec_iff).mpr ⟨hπ₁Node, hρ₁Node, d₁, τ₁, rfl⟩
  obtain ⟨⟨σ₁, hIO₁, hII₁⟩, hOut₁⟩ :=
    hlin π₁ (π₁ ++ d₁ :: τ₁) p₁ q₁ p₂ q₂ k hprec₁ hlblπ₁ hlblρ₁
  have htrIn₁ : TraceInputDep (p₁, q₁, k) (halfOpenLabels H₁ (π₁ ++ [d₁]) τ₁) (p₂, q₂, k) :=
    traceInputDep_of_reflTransGen_precIO hIO₁ hII₁ hlblπ₁ hlblρ₁
  have htrOut₁ : TraceOutputDep (p₁, q₁, k) (halfOpenLabels H₁ (π₁ ++ [d₁]) τ₁) (p₂, q₂, k) :=
    traceOutputDep_of_outputDep hOut₁ rfl hlblπ₁ hlblρ₁
  have htrIn₂ := TraceInputDep.sublist hsub htrIn₁
  have htrOut₂ := TraceOutputDep.sublist hsub htrOut₁
  exact ⟨inputDep_of_traceInputDep h₂ τ (List.prefix_refl π) hlblπ hlblρ htrIn₂,
         outputDep_of_traceOutputDep h₂ τ (List.prefix_refl π) hlblπ hlblρ htrOut₂⟩

end SolMPSTProp3131

theorem solution (G : GType) (_hG : WellFormed G) (n : ℕ) (hn : 1 ≤ n) :
    Linear (unfold 1 G) ↔ Linear (unfold n G) := by
  constructor
  · rintro ⟨hMain, hCarried⟩
    refine ⟨?_, ?_⟩
    · exact SolMPSTProp3131.TraceSim.mainLinear
        (SolMPSTProp3131.traceSim_unfold n G)
        (SolMPSTProp3131.MuFree.unfold 1 G)
        (SolMPSTProp3131.MuFree.unfold n G) hMain
    · intro H hH m
      apply hCarried H
      rwa [SolMPSTProp3131.carried_unfold_iff, ← SolMPSTProp3131.carried_unfold_iff n]
  · rintro ⟨hMain, hCarried⟩
    refine ⟨?_, ?_⟩
    · exact SolMPSTProp3131.approx_mainLinear
        (SolMPSTProp3131.approx_unfold hn G)
        (SolMPSTProp3131.MuFree.unfold 1 G)
        (SolMPSTProp3131.MuFree.unfold n G) hMain
    · intro H hH m
      apply hCarried H
      rwa [SolMPSTProp3131.carried_unfold_iff, ← SolMPSTProp3131.carried_unfold_iff 1]
