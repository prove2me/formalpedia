-- Prove2me | solution 1 for LodhaMoore.presentation_G_G0Seq_and_isFinitelyPresented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.788022+00:00
-- url     : https://prove2.me/submissions/03da6162-f3ee-4004-a60f-00fca96375f6

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_LodhaMooreWords
import Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
import Theorems.Thm_LodhaMoore_exists_presentation_F_and_mulEquiv_F2
import Theorems.Thm_LodhaMoore_isFinitelyPresented_of_presentation
import Theorems.Thm_LodhaMoore_exists_derives_standardForm_le_depth
import Theorems.Thm_LodhaMoore_exists_derives_sufficientlyExpanded
import Theorems.Thm_LodhaMoore_isXWord_or_eval_ne_of_sufficientlyExpanded
section
/-!
# Lodha–Moore: Theorem 3.3 and Theorem 1.1

Theorem 3.3 (`R` presents `G`, `R₀` presents `G₀`, both finitely presented) by the argument at the
end of §5, and Theorem 1.1 (the goal).
-/

namespace LodhaMoore.Dev.Top

open LodhaMoore

/-! ### Constant sequences -/

lemma not_isConst_iff (t : Seq) : ¬ IsConst t ↔ true ∈ t ∧ false ∈ t := by
  constructor
  · intro h
    unfold IsConst at h
    push Not at h
    obtain ⟨i, hi, j, hj, hne⟩ := h
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hne
    have h1 := List.getElem_mem hi
    have h2 := List.getElem_mem hj
    cases hti : t[i] <;> cases htj : t[j] <;> simp_all
  · rintro ⟨ht, hf⟩ h
    obtain ⟨i, hi, hti⟩ := List.getElem_of_mem ht
    obtain ⟨j, hj, htj⟩ := List.getElem_of_mem hf
    have := h i hi j hj
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, hti, htj] at this
    simp at this

lemma inS0_y (s : Seq) : (Gen.y s).InS0 ↔ true ∈ s ∧ false ∈ s := not_isConst_iff s

lemma inS0_y_append {s : Seq} (l : Seq) (h : (Gen.y s).InS0) : (Gen.y (s ++ l)).InS0 := by
  rw [inS0_y] at h ⊢
  simp [h.1, h.2]

lemma inS0_y_xFin {s t t' : Seq} (h : xFin s t = some t') (ht : (Gen.y t).InS0) :
    (Gen.y t').InS0 := by
  rw [inS0_y] at ht ⊢
  unfold xFin at h
  split_ifs at h with h1 h2
  · obtain ⟨r, rfl⟩ := h1
    rw [List.drop_left] at h
    rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp at h <;> subst h <;> simp_all
  · simp at h; subst h; exact ht

lemma inS0_y_xFinInv {s t t' : Seq} (h : xFinInv s t = some t') (ht : (Gen.y t).InS0) :
    (Gen.y t').InS0 := by
  rw [inS0_y] at ht ⊢
  unfold xFinInv at h
  split_ifs at h with h1 h2
  · obtain ⟨r, rfl⟩ := h1
    rw [List.drop_left] at h
    rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp at h <;> subst h <;> simp_all
  · simp at h; subst h; exact ht

/-- `t.x_s⁻¹ = t'` gives `t'.x_s = t`. -/
lemma xFin_of_xFinInv {s t t' : Seq} (h : xFinInv s t = some t') : xFin s t' = some t := by
  unfold xFinInv at h
  split_ifs at h with h1 h2
  · obtain ⟨r, rfl⟩ := h1
    rw [List.drop_left] at h
    rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp at h <;> subst h <;> simp [xFin]
  · simp at h; subst h
    simp [xFin, h1, h2]


/-! ### Words evaluated in an arbitrary group -/

section EvalW

variable {H : Type*} [Group H]

/-- The value of a word when the generator `g` is sent to `f g`, multiplied left to right. -/
def evalW (f : Gen → H) (Ω : Word) : H := (Ω.map fun p => f p.1 ^ p.2).prod

@[simp] lemma evalW_nil (f : Gen → H) : evalW f [] = 1 := rfl

@[simp] lemma evalW_cons (f : Gen → H) (p : Gen × ℤ) (Ω : Word) :
    evalW f (p :: Ω) = f p.1 ^ p.2 * evalW f Ω := by
  simp [evalW]

@[simp] lemma evalW_append (f : Gen → H) (A B : Word) :
    evalW f (A ++ B) = evalW f A * evalW f B := by
  simp [evalW]

lemma evalW_map {K : Type*} [Group K] (π : H →* K) (f : Gen → H) (Ω : Word) :
    π (evalW f Ω) = evalW (π ∘ f) Ω := by
  induction Ω with
  | nil => simp
  | cons p Ω ih => simp [ih]

lemma eval_eq_evalW (Ω : Word) : Ω.eval = evalW Gen.val Ω := rfl

lemma evalW_congr {f f' : Gen → H} {Ω : Word} (h : ∀ p ∈ Ω, f p.1 = f' p.1) :
    evalW f Ω = evalW f' Ω := by
  induction Ω with
  | nil => rfl
  | cons p Ω ih =>
    simp only [evalW_cons]
    rw [h p (by simp), ih (fun q hq => h q (by simp [hq]))]

/-- The hypotheses under which a derivation preserves the value of a word whose letters satisfy
`P`: the relations among letters satisfying `P` hold, and the substitutions keep the letters in
`P`. -/
structure Good (P : Gen → Prop) (f : Gen → H) : Prop where
  rel : ∀ r : Rel, (∀ g ∈ r.gens, P g) → FreeGroup.lift f (r.lhs * r.rhs⁻¹) = 1
  x : ∀ s, P (.x s)
  ext : ∀ s l, P (.y s) → P (.y (s ++ l))
  move : ∀ s t t', xFin s t = some t' → P (.y t) → P (.y t')
  moveInv : ∀ s t t', xFinInv s t = some t' → P (.y t) → P (.y t')

lemma Good.rel' {P : Gen → Prop} {f : Gen → H} (hG : Good P f) (r : Rel)
    (h : ∀ g ∈ r.gens, P g) : FreeGroup.lift f r.lhs = FreeGroup.lift f r.rhs := by
  have := hG.rel r h
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

lemma P_replace {P : Gen → Prop} {pre post L L' : Word} (hP : ∀ p ∈ pre ++ L ++ post, P p.1)
    (hL' : ∀ p ∈ L', P p.1) : ∀ p ∈ pre ++ L' ++ post, P p.1 := by
  intro p hp
  simp only [List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · exact hP p (by simp [hp])
  · exact hL' p hp
  · exact hP p (by simp [hp])

lemma P_mid {P : Gen → Prop} {pre post L : Word} (hP : ∀ p ∈ pre ++ L ++ post, P p.1) :
    ∀ p ∈ L, P p.1 := fun p hp => hP p (by simp [hp])

/-- One substitution preserves the value of a word whose letters satisfy `P`, and keeps its
letters in `P`. -/
lemma step_good {P : Gen → Prop} {f : Gen → H} (hG : Good P f) {Ω Ω' : Word} (h : Step Ω Ω')
    (hP : ∀ p ∈ Ω, P p.1) : evalW f Ω = evalW f Ω' ∧ ∀ p ∈ Ω', P p.1 := by
  cases h with
  | moveX pre post s t t' i h =>
    have hL := P_mid hP
    have hyt : P (.y t) := hL (.y t, i) (by simp)
    have hyt' : P (.y t') := hG.move s t t' h hyt
    have hr := hG.rel' (.three s t t' h) (by simp [Rel.gens, hyt, hyt', hG.x])
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of] at hr
    have hs : SemiconjBy (f (.x s)) (f (.y t')) (f (.y t)) := hr.symm
    refine ⟨?_, P_replace hP ?_⟩
    · simp only [evalW_append, evalW_cons, evalW_nil, mul_one, zpow_one]
      rw [(hs.zpow_right i).eq]
    · simp [hG.x, hyt']
  | moveXInv pre post s t t' i h =>
    have hL := P_mid hP
    have hyt : P (.y t) := hL (.y t, i) (by simp)
    have hyt' : P (.y t') := hG.moveInv s t t' h hyt
    have h' := xFin_of_xFinInv h
    have hr := hG.rel' (.three s t' t h') (by simp [Rel.gens, hyt, hyt', hG.x])
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of] at hr
    have hs : SemiconjBy (f (.x s)) (f (.y t)) (f (.y t')) := hr.symm
    refine ⟨?_, P_replace hP ?_⟩
    · simp only [evalW_append, evalW_cons, evalW_nil, mul_one, zpow_neg, zpow_one]
      have := (hs.zpow_right i).eq
      congr 2
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, this, mul_assoc, mul_inv_cancel, mul_one]
    · simp [hG.x, hyt']
  | expand pre post s =>
    have hL := P_mid hP
    have hys : P (.y s) := hL (.y s, 1) (by simp)
    have hr := hG.rel' (.five s) (by simp [Rel.gens, hys, hG.x, hG.ext s _ hys])
    simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of] at hr
    refine ⟨?_, P_replace hP ?_⟩
    · simp only [evalW_append, evalW_cons, evalW_nil, mul_one, zpow_neg, zpow_one]
      rw [hr]
      simp only [mul_assoc]
    · simp [hG.x, hG.ext s _ hys]
  | expandInv pre post s =>
    have hL := P_mid hP
    have hys : P (.y s) := hL (.y s, -1) (by simp)
    have hx := hG.x s
    have he := hG.ext s
    have h5 := hG.rel' (.five s) (by simp [Rel.gens, hys, hx, he _ hys])
    have hA := hG.rel' (.three s (s ++ [false, false]) (s ++ [false]) (by simp [xFin]))
      (by simp [Rel.gens, hx, he _ hys])
    have hB := hG.rel' (.three s (s ++ [false, true]) (s ++ [true, false]) (by simp [xFin]))
      (by simp [Rel.gens, hx, he _ hys])
    have hC := hG.rel' (.three s (s ++ [true]) (s ++ [true, true]) (by simp [xFin]))
      (by simp [Rel.gens, hx, he _ hys])
    have hAB := hG.rel' (.four (s ++ [false]) (s ++ [true, false]) (by
      constructor <;> simp [List.prefix_append_right_inj])) (by simp [Rel.gens, he _ hys])
    have hAC := hG.rel' (.four (s ++ [false]) (s ++ [true, true]) (by
      constructor <;> simp [List.prefix_append_right_inj])) (by simp [Rel.gens, he _ hys])
    have hBC := hG.rel' (.four (s ++ [true, false]) (s ++ [true, true]) (by
      constructor <;> simp [List.prefix_append_right_inj])) (by simp [Rel.gens, he _ hys])
    simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of] at h5 hA hB hC hAB hAC hBC
    refine ⟨?_, P_replace hP ?_⟩
    · simp only [evalW_append, evalW_cons, evalW_nil, mul_one, zpow_neg, zpow_one]
      congr 2
      set X := f (Gen.x s)
      set A := f (Gen.y (s ++ [false]))
      set B := f (Gen.y (s ++ [true, false]))
      set C := f (Gen.y (s ++ [true, true]))
      rw [h5, eq_mul_inv_of_mul_eq hA, eq_mul_inv_of_mul_eq hB, eq_mul_inv_of_mul_eq hC]
      have cAB : Commute A B := hAB
      have cAC : Commute A C := hAC
      have cBC : Commute B C := hBC
      have key : C⁻¹ * B * A⁻¹ = A⁻¹ * B * C⁻¹ := by
        rw [((cAC.inv_right.mul_right cAB).inv_left).eq.symm, cBC.inv_right.eq.symm, mul_assoc]
      calc (X * A * B⁻¹ * C)⁻¹ = C⁻¹ * B * A⁻¹ * X⁻¹ := by group
        _ = A⁻¹ * B * C⁻¹ * X⁻¹ := by rw [key]
        _ = _ := by group
    · simp [hx, he _ hys]
  | commute pre post u v i j h =>
    have hL := P_mid hP
    have hu : P (.y u) := hL (.y u, i) (by simp)
    have hv : P (.y v) := hL (.y v, j) (by simp)
    have hr := hG.rel' (.four u v h) (by simp [Rel.gens, hu, hv])
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of] at hr
    have hc : Commute (f (.y u)) (f (.y v)) := hr
    refine ⟨?_, P_replace hP ?_⟩
    · simp only [evalW_append, evalW_cons, evalW_nil, mul_one]
      rw [(hc.zpow_zpow i j).eq]
    · simp [hu, hv]
  | split pre post g i j hi hj hij =>
    have hL := P_mid hP
    have hg : P g := hL (g, i + j) (by simp)
    refine ⟨?_, P_replace hP ?_⟩
    · simp [zpow_add, mul_assoc]
    · simp [hg]
  | merge pre post g i j hi hj hij =>
    have hL := P_mid hP
    have hg : P g := hL (g, i) (by simp)
    refine ⟨?_, P_replace hP ?_⟩
    · simp [zpow_add, mul_assoc]
    · simp [hg]
  | cancel pre post s i hi =>
    refine ⟨?_, ?_⟩
    · simp
    · intro p hp
      exact hP p (by simp only [List.mem_append] at hp ⊢; tauto)

lemma derives_good {P : Gen → Prop} {f : Gen → H} (hG : Good P f) {Ω Ω' : Word}
    (h : Derives Ω Ω') (hP : ∀ p ∈ Ω, P p.1) : evalW f Ω = evalW f Ω' ∧ ∀ p ∈ Ω', P p.1 := by
  induction h with
  | refl => exact ⟨rfl, hP⟩
  | tail _ hst ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := step_good hG hst h2
    exact ⟨h1.trans h3, h4⟩

end EvalW

/-! ### From a derivation to the presentation (end of §5) -/

section Inj

variable {H : Type*} [Group H]

/-- A word for an element of a free group, its generators relabelled by `ι`. -/
def toW {α : Type*} [DecidableEq α] (ι : α → Gen) (v : FreeGroup α) : Word :=
  v.toWord.map fun p => (ι p.1, if p.2 then 1 else -1)

lemma evalW_toW {α : Type*} [DecidableEq α] (ι : α → Gen) (f : Gen → H) (v : FreeGroup α) :
    evalW f (toW ι v) = FreeGroup.lift (f ∘ ι) v := by
  conv_rhs => rw [← FreeGroup.mk_toWord (x := v)]
  rw [FreeGroup.lift_mk]
  simp only [evalW, toW, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b <;> simp

lemma isWord_toW {α : Type*} [DecidableEq α] (ι : α → Gen) (v : FreeGroup α) : IsWord (toW ι v) := by
  intro p hp
  simp only [toW, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  cases q.2 <;> simp

lemma mem_toW {α : Type*} [DecidableEq α] {ι : α → Gen} {v : FreeGroup α} {p : Gen × ℤ} (hp : p ∈ toW ι v) :
    ∃ a, p.1 = ι a := by
  simp only [toW, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact ⟨q.1, rfl⟩

lemma lift_of_eq_mk {α : Type*} (rels : Set (FreeGroup α)) :
    FreeGroup.lift (PresentedGroup.of : α → PresentedGroup rels) = PresentedGroup.mk rels :=
  FreeGroup.ext_hom _ _ fun a => by simp [PresentedGroup.of]

/-- The heart of Theorem 3.3 (end of §5): if a word whose letters satisfy `P` evaluates to the
identity of `SeqGroup`, then it is the identity in any group in which the relations among the
letters satisfying `P` hold. By Lemmas 5.4 and 5.6 it derives a sufficiently expanded standard
form, which by Lemma 5.11 is an `X`-word, and the relations (1), (2) present `F`. -/
theorem evalW_eq_one {P : Gen → Prop} {f : Gen → H} (hG : Good P f) (π : H →* SeqGroup)
    (hπ : ∀ g, P g → π (f g) = g.val) (Ω : Word) (hΩ : IsWord Ω) (hP : ∀ p ∈ Ω, P p.1)
    (h1 : π (evalW f Ω) = 1) : evalW f Ω = 1 := by
  obtain ⟨Ω1, d1, sf1, -⟩ := exists_derives_standardForm_le_depth Ω hΩ 0
  obtain ⟨Ω2, d2, sf2, se2⟩ := exists_derives_sufficientlyExpanded Ω1 sf1
  obtain ⟨e1, p1⟩ := derives_good hG d1 hP
  obtain ⟨e2, p2⟩ := derives_good hG d2 p1
  have hev : Ω2.eval = 1 := by
    rw [eval_eq_evalW, ← evalW_congr (f := π ∘ f) (fun p hp => hπ _ (p2 p hp)), ← evalW_map,
      ← e2, ← e1, h1]
  have hX : IsXWord Ω2 := by
    rcases isXWord_or_eval_ne_of_sufficientlyExpanded Ω2 sf2 se2 with h | h
    · exact h
    · exact absurd hev (h [] ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩)
  obtain ⟨⟨φF, hφF, hinj, -⟩, -⟩ := exists_presentation_F_and_mulEquiv_F2
  have hRX : ∀ r ∈ RX, FreeGroup.lift (fun s => f (.x s)) r = 1 := by
    rintro r (⟨s, rfl⟩ | ⟨s, t, t', h, rfl⟩)
    · have := hG.rel (.one s) (by simp [Rel.gens, hG.x])
      simpa [Rel.lhs, Rel.rhs] using this
    · have := hG.rel (.two s t t' h) (by simp [Rel.gens, hG.x])
      simpa [Rel.lhs, Rel.rhs] using this
  let ρ := PresentedGroup.toGroup hRX
  have hcomp : π.comp ρ = φF := PresentedGroup.ext fun s => by
    simp [ρ, hφF, hπ _ (hG.x s), Gen.val]
  let fX : Gen → PresentedGroup RX := fun g => match g with
    | .x s => PresentedGroup.of s
    | .y _ => 1
  have hρ : evalW f Ω2 = ρ (evalW fX Ω2) := by
    rw [evalW_map]
    apply evalW_congr
    intro p hp
    obtain ⟨s, hs⟩ := hX.2 p hp
    rw [hs]
    simp [fX, ρ]
  have hz : evalW fX Ω2 = 1 := hinj (by
    rw [map_one, ← hcomp, MonoidHom.comp_apply, ← hρ, ← e2, ← e1, h1])
  rw [e1, e2, hρ, hz, map_one]

/-- `R` presents `G`. -/
theorem presentation_R : ∃ phi : PresentedGroup R →* SeqGroup,
    (∀ g, phi (PresentedGroup.of g) = g.val) ∧ Function.Injective phi ∧ phi.range = G := by
  have hR := bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2
  refine ⟨PresentedGroup.toGroup hR, fun g => PresentedGroup.toGroup.of hR, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨v, rfl⟩ := PresentedGroup.mk_surjective R w
    have hG : Good (fun _ => True) (PresentedGroup.of : Gen → PresentedGroup R) :=
      { rel := fun r _ => by
          rw [lift_of_eq_mk]
          exact PresentedGroup.one_of_mem ⟨r, rfl⟩
        x := fun _ => trivial
        ext := fun _ _ _ => trivial
        move := fun _ _ _ _ _ => trivial
        moveInv := fun _ _ _ _ _ => trivial }
    have hv : evalW PresentedGroup.of (toW id v) = PresentedGroup.mk R v := by
      rw [evalW_toW, Function.comp_id, lift_of_eq_mk]
    rw [← hv] at hw ⊢
    exact evalW_eq_one hG (PresentedGroup.toGroup hR) (fun g _ => PresentedGroup.toGroup.of hR) _
      (isWord_toW _ _) (fun _ _ => trivial) hw
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    unfold G
    congr 1
    ext z
    simp only [Set.mem_range, Function.comp_apply, PresentedGroup.toGroup.of, Set.mem_union]
    constructor
    · rintro ⟨(s | s), rfl⟩
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr ⟨s, rfl⟩
    · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
      · exact ⟨.x s, rfl⟩
      · exact ⟨.y s, rfl⟩

lemma lift_map_val {K : Type*} [Group K] (f : Gen → K) (w : FreeGroup GenS0) :
    FreeGroup.lift f (FreeGroup.map Subtype.val w) = FreeGroup.lift (f ∘ Subtype.val) w := by
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun a => by simp

/-- A relation all of whose generators lie in `S₀` is a word in `S₀`. -/
lemma mem_range_map_val (r : Rel) (h : ∀ g ∈ r.gens, g.InS0) :
    r.lhs * r.rhs⁻¹ ∈ (FreeGroup.map (Subtype.val : GenS0 → Gen)).range := by
  have hof : ∀ g, g.InS0 → FreeGroup.of g ∈ (FreeGroup.map (Subtype.val : GenS0 → Gen)).range :=
    fun g hg => ⟨FreeGroup.of ⟨g, hg⟩, by simp⟩
  cases r <;> simp only [Rel.gens, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [Rel.lhs, Rel.rhs] <;>
    repeat' (first | apply mul_mem | apply inv_mem | apply hof)
  all_goals tauto

open Classical in
/-- The generators of `S₀` in the presented group `⟨S₀ | R₀⟩`, the others sent to `1`. -/
noncomputable def f0 (g : Gen) : PresentedGroup R0S :=
  if h : g.InS0 then PresentedGroup.of ⟨g, h⟩ else 1

lemma f0_val (g : GenS0) : f0 g.1 = PresentedGroup.of g := by
  simp [f0, g.2]

lemma good_f0 : Good Gen.InS0 f0 where
  rel r h := by
    obtain ⟨w, hw⟩ := mem_range_map_val r h
    rw [← hw, lift_map_val]
    have : f0 ∘ Subtype.val = PresentedGroup.of := funext f0_val
    rw [this, lift_of_eq_mk]
    exact PresentedGroup.one_of_mem (show FreeGroup.map Subtype.val w ∈ R0 from hw ▸ ⟨r, h, rfl⟩)
  x _ := trivial
  ext _ l h := inS0_y_append l h
  move _ _ _ h ht := inS0_y_xFin h ht
  moveInv _ _ _ h ht := inS0_y_xFinInv h ht

/-- `R₀` presents `G₀` (as `G0Seq`). -/
theorem presentation_R0 : ∃ phi : PresentedGroup R0S →* SeqGroup,
    (∀ g, phi (PresentedGroup.of g) = g.1.val) ∧ Function.Injective phi ∧ phi.range = G0Seq := by
  have hR := bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2
  have hR0 : ∀ r ∈ R0S, FreeGroup.lift (fun g : GenS0 => g.1.val) r = 1 := by
    intro r hr
    have : (fun g : GenS0 => g.1.val) = Gen.val ∘ Subtype.val := rfl
    rw [this, ← lift_map_val]
    obtain ⟨q, -, hq⟩ := hr
    exact hR _ ⟨q, hq⟩
  refine ⟨PresentedGroup.toGroup hR0, fun g => PresentedGroup.toGroup.of hR0, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨v, rfl⟩ := PresentedGroup.mk_surjective R0S w
    have hv : evalW f0 (toW Subtype.val v) = PresentedGroup.mk R0S v := by
      rw [evalW_toW, show f0 ∘ Subtype.val = PresentedGroup.of from funext f0_val,
        lift_of_eq_mk]
    rw [← hv] at hw ⊢
    refine evalW_eq_one good_f0 (PresentedGroup.toGroup hR0) (fun g hg => ?_) _
      (isWord_toW _ _) (fun p hp => ?_) hw
    · rw [f0_val ⟨g, hg⟩, PresentedGroup.toGroup.of]
    · obtain ⟨a, ha⟩ := mem_toW hp
      rw [ha]
      exact a.2
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    unfold G0Seq
    congr 1
    ext z
    simp only [Set.mem_range, Function.comp_apply, PresentedGroup.toGroup.of, Set.mem_union,
      Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨(s | s), hs⟩, rfl⟩
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr ⟨s, hs, rfl⟩
    · rintro (⟨s, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨⟨.x s, trivial⟩, rfl⟩
      · exact ⟨⟨.y s, hs⟩, rfl⟩

end Inj

/-! ### Theorem 1.1: nonamenability (§2) -/

section Amen

open MeasureTheory

/-- Homeomorphisms of the projective line act on it by evaluation. -/
abbrev mulActionHomeo : MulAction (OnePoint ℝ ≃ₜ OnePoint ℝ) (OnePoint ℝ) where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] mulActionHomeo

end Amen

end LodhaMoore.Dev.Top

namespace LodhaMoore

open LodhaMoore.Dev.Top

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.Top
theorem solution :
    (∃ phi : PresentedGroup R →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.val) ∧
      Function.Injective phi ∧ phi.range = G) ∧
    (∃ phi : PresentedGroup R0S →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.1.val) ∧
      Function.Injective phi ∧ phi.range = G0Seq) ∧
    Group.IsFinitelyPresented G ∧ Group.IsFinitelyPresented G0Seq :=
  ⟨presentation_R, presentation_R0, isFinitelyPresented_of_presentation.1 presentation_R,
    isFinitelyPresented_of_presentation.2 presentation_R0⟩
end
