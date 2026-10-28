-- Prove2me | solution 1 for OAI.RowColumn.MatrixState.occupied_commutant_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:04:02.511974+00:00
-- url     : https://prove2.me/submissions/16409ca9-a39d-4591-9b72-195fe4226e63

import Mathlib
import Definitions.Def_OccupiedOverlap
import Definitions.Def_OAIW2RC000
import Theorems.Thm_OAI_RowColumn_MatrixState_sector_filtered_trace_bound

section
-- module Solutions.OAIW2_RowColumn.Compat
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_HilbertSchmidt
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [Fintype J]

variable [DecidableEq I]

lemma trace_mul_psd_nonneg (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let R : Matrix I I ℂ := CFC.sqrt B
  have hs : R.conjTranspose=R := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hsq : R*R=B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hh := (hA.conjTranspose_mul_mul_same R).trace_nonneg
  rw [hs] at hh
  have ht : (R*A*R).trace=(A*B).trace := by
    rw [Matrix.trace_mul_cycle,hsq,Matrix.trace_mul_comm]
  rw [ht] at hh
  exact hh.1

lemma trace_mul_mono (A B T : Matrix I I ℂ) (h : A ≤ B) (hT : T.PosSemidef) :
    (A*T).trace.re ≤ (B*T).trace.re := by
  have hh := trace_mul_psd_nonneg (B-A) T h hT
  rw [sub_mul,Matrix.trace_sub,Complex.sub_re] at hh
  linarith

end RowColumn.MatrixState

end
end

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

lemma toEuclideanCLM_positive_iff (A : Matrix I I ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact Matrix.isPositive_toEuclideanLin_iff

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.YoungSymmetry_Polytabloid
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary polytabloid input for the symmetric-group step of FAC.7.
No branching or classification theorem is postulated here. -/
namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma permSign_sq {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    permSign p * permSign p = 1 := by
  calc
    permSign p * permSign p = permSign (p*p⁻¹) := by rw [permSign_mul,permSign_inv]
    _ = 1 := by simp
end CubeShuffle.Specht

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_SignedWords
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma word_stabilizer_eq (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (x : S) : w.1 (g x) = w.1 x := by
  have he := congrArg (fun z : Words (S := S) odd k => z.1 (g x)) hw
  simpa using he.symm

omit [Fintype C] [DecidableEq C] in
lemma oddPerm_sign_of_stabilizes (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (hfix : ∀ x, ¬ odd (w.1 x) → g x = x) :
    permSign (oddPerm g w) = permSign g := by
  have hs : ∀ x, odd (w.1 (g x)) ↔ odd (w.1 x) := fun x => by
    rw [word_stabilizer_eq g w hw x]
  have he := Equiv.Perm.sign_eq_sign_of_equiv (g.subtypePerm hs)
    (oddPerm g w) (oddFrame w) (by
      intro x
      change oddFrame w ⟨g x.1, _⟩ =
        oddFrame (actWord g w)
          ((relabelOddEquiv g w.1) ((oddFrame w).symm (oddFrame w x)))
      erw [Equiv.symm_apply_apply]
      exact (oddFrame_congr hw (g x.1) _ _).symm)
  have hf : ∀ x, g x ≠ x → odd (w.1 x) := by
    intro x hn
    by_contra h
    exact hn (hfix x h)
  rw [Equiv.Perm.sign_subtypePerm g hs hf] at he
  exact congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) he.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_of_odd_fixed (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (hfix : ∀ x, odd (w.1 x) → g x = x) :
    oddPerm g w = 1 := by
  apply Equiv.ext
  intro i
  let x := (oddFrame w).symm i
  change oddFrame (actWord g w) ⟨g x.1, _⟩ = i
  have he := oddFrame_congr hw (g x.1)
    (show odd ((actWord g w).1 (g x.1)) by simpa using x.2)
    (by rw [hfix x.1 x.2]; exact x.2)
  refine he.trans ?_
  have hh : (⟨g x.1, by rw [hfix x.1 x.2]; exact x.2⟩ : OddSlots w) = x :=
    Subtype.ext (hfix x.1 x.2)
  rw [hh]
  exact (oddFrame w).apply_symm_apply i

end RowColumn.Signed

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_inv (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    oddPerm g⁻¹ (actWord g w) = (oddPerm g w)⁻¹ := by
  have hh := oddPerm_mul g⁻¹ g w
  rw [inv_mul_cancel, oddPerm_one] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma signedMap_transport_apply (g : Equiv.Perm S)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) (w : Words (S := S) odd k) :
    representation g x (actWord g w) = permSign (oddPerm g w) * x w := by
  change permSign (oddPerm g⁻¹ (actWord g w)) * x (actWord g⁻¹ (actWord g w)) = _
  rw [oddPerm_inv, permSign_inv, ← actWord_mul, inv_mul_cancel, actWord_one]

omit [DecidableEq S] [Fintype C] in
lemma signedMap_wordVector (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    representation g (wordVector w) = permSign (oddPerm g w) • wordVector (actWord g w) := by
  ext z
  obtain ⟨v, rfl⟩ := (wordsEquiv g).surjective z
  change representation g (wordVector w) (actWord g v) = _
  rw [signedMap_transport_apply]
  change permSign (oddPerm g v) * (if v = w then (1 : ℂ) else 0) =
    permSign (oddPerm g w) * (if actWord g v = actWord g w then (1 : ℂ) else 0)
  have he : actWord g v = actWord g w ↔ v = w := (wordsEquiv g).apply_eq_iff_eq
  simp only [he]
  by_cases hv : v = w
  · subst v; rfl
  · simp [hv]

lemma sum_wordVectors (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    (∑ w, x w • wordVector w) = x := by
  ext z
  simp [WithLp.ofLp_sum, wordVector, WithLp.ofLp_smul]

variable {L : Type*} [Fintype L] [DecidableEq L] (line : S → L)

omit [Fintype L] [DecidableEq L] [DecidableEq S] [Fintype C] in
lemma commuting_coefficient_relation
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (g : RowColumn.lineGroup line) (w v : Words (S := S) odd k) :
    permSign (oddPerm g.1 v) * T (wordVector (actWord g.1 v)) (actWord g.1 w) =
    permSign (oddPerm g.1 w) * T (wordVector v) w := by
  have he := congrArg (fun x : EuclideanSpace ℂ (Words (S := S) odd k) => x (actWord g.1 w))
    (Representation.IntertwiningMap.isIntertwining _ _ T g (wordVector v))
  change T (representation g.1 (wordVector v)) (actWord g.1 w) =
    representation g.1 (T (wordVector v)) (actWord g.1 w) at he
  rw [signedMap_wordVector, map_smul, signedMap_transport_apply] at he
  exact he

end RowColumn.Signed

end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_Postselection
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Nat
namespace RowColumn.WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma card_transporters (a b : S → A) (he : counts a = counts b) :
    Fintype.card {p : Equiv.Perm S // ∀ x, b (p x) = a x} =
      ∏ c : A, (Fintype.card {x : S // a x = c})! := by
  rw [Fintype.card_congr (transporterEquiv a b), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  have hc : Fintype.card {x : S // a x = c} = Fintype.card {x : S // b x = c} :=
    congrArg (fun f : A → Fin (Fintype.card S + 1) => (f c).val) he
  let e := Fintype.equivOfCardEq hc
  let ee : ({x : S // a x = c} ≃ {x : S // b x = c}) ≃
      Equiv.Perm {x : S // a x = c} :=
    { toFun := fun f => f.trans e.symm
      invFun := fun g => g.trans e
      left_inv := by intro f; ext x; simp
      right_inv := by intro g; ext x; simp }
  rw [Fintype.card_congr ee, Fintype.card_perm]

/-- Orbit-stabilizer with all factors explicit. It is the exact multinomial
cardinality needed for the finite postselection probability. -/
lemma type_card_factorial (a : S → A) :
    Fintype.card {b : S → A // counts b = counts a} *
      (∏ c : A, (Fintype.card {x : S // a x = c})!) = (Fintype.card S)! := by
  let e : Equiv.Perm S ≃
      Σ b : {b : S → A // counts b = counts a},
        {p : Equiv.Perm S // ∀ x, b.1 (p x) = a x} :=
    { toFun := fun p =>
        ⟨⟨(fun x => a (p.symm x)), by
          funext c
          apply Fin.ext
          exact Fintype.card_congr
            { toFun := fun x => ⟨p.symm x.1,x.2⟩
              invFun := fun x => ⟨p x.1,by simpa using x.2⟩
              left_inv := by intro x; apply Subtype.ext; simp
              right_inv := by intro x; apply Subtype.ext; simp }⟩,
          ⟨p,fun x => by simp⟩⟩
      invFun := fun z => z.2.1
      left_inv := by intro p; rfl
      right_inv := by
        rintro ⟨⟨b,hb⟩,p,hp⟩
        have he : (fun x => a (p.symm x)) = b := by
          funext x
          have h := hp (p.symm x)
          simpa using h.symm
        cases he
        rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_perm, Fintype.card_sigma] at hc
  have hn (b : {b : S → A // counts b = counts a}) :
      Fintype.card {p : Equiv.Perm S // ∀ x, b.1 (p x) = a x} =
        ∏ c : A, (Fintype.card {x : S // a x = c})! :=
    card_transporters a b.1 b.2.symm
  simp_rw [hn] at hc
  simpa using hc.symm

end RowColumn.WordOrbits

namespace RowColumn.WordOrbits
open scoped BigOperators Classical Nat

lemma factorial_le_factorial_mul_pow {b a : ℕ} (h : b ≤ a) :
    a.factorial ≤ b.factorial * a^(a-b) := by
  induction a,h using Nat.le_induction with
  | base => simp
  | succ a ha ih =>
    rw [Nat.factorial_succ, show a+1-b = (a-b)+1 by omega, pow_succ]
    calc
      (a+1)*a.factorial ≤ (a+1)*(b.factorial*a^(a-b)) := Nat.mul_le_mul_left _ ih
      _ ≤ (a+1)*(b.factorial*(a+1)^(a-b)) := by gcongr; omega
      _ = _ := by ring

lemma factorial_mode (a b : ℕ) : a^b * a.factorial ≤ a^a * b.factorial := by
  rcases le_total a b with h | h
  · have hh := Nat.factorial_mul_pow_sub_le_factorial h
    calc
      a^b * a.factorial = a^a * (a.factorial * a^(b-a)) := by
        calc
          _ = a^(a+(b-a)) * a.factorial := by rw [Nat.add_sub_of_le h]
          _ = _ := by rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hh
  · have hh := factorial_le_factorial_mul_pow h
    calc
      a^b * a.factorial ≤ a^b * (b.factorial * a^(a-b)) := Nat.mul_le_mul_left _ hh
      _ = a^a * b.factorial := by
        calc
          _ = a^(b+(a-b)) * b.factorial := by rw [pow_add]; ring
          _ = _ := by rw [Nat.add_sub_of_le h]

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] in
lemma sum_counts (w : S → A) : ∑ c : A, (counts w c).val = Fintype.card S := by
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv w)).symm.trans (by rw [Fintype.card_sigma]; rfl) |>.symm

/-- Under its own empirical product distribution, a type is a mode among
all types. This gives a polynomial lower bound without Stirling or entropy. -/
lemma empirical_type_mode (a b : S → A) :
    Fintype.card {w : S → A // counts w = counts b} *
      (∏ c : A, (counts a c).val ^ (counts b c).val) ≤
    Fintype.card {w : S → A // counts w = counts a} *
      (∏ c : A, (counts a c).val ^ (counts a c).val) := by
  have h := Finset.prod_le_prod' (fun c (_ : c ∈ Finset.univ) =>
    factorial_mode (counts a c).val (counts b c).val)
  simp only [Finset.prod_mul_distrib] at h
  have ha := type_card_factorial a
  have hb := type_card_factorial b
  change _ * (∏ c : A, (counts a c).val !) = _ at ha
  change _ * (∏ c : A, (counts b c).val !) = _ at hb
  have hp : 0 < (∏ c : A, (counts a c).val !) * (∏ c : A, (counts b c).val !) := by
    exact Nat.mul_pos (Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
      (Finset.prod_pos (fun _ _ => Nat.factorial_pos _))
  apply (Nat.mul_le_mul_right_iff hp).mp
  calc
    _ = (Fintype.card S)! * ((∏ c, (counts a c).val ^ (counts b c).val) *
        ∏ c, (counts a c).val !) := by rw [← hb]; ring
    _ ≤ (Fintype.card S)! * ((∏ c, (counts a c).val ^ (counts a c).val) *
        ∏ c, (counts b c).val !) := Nat.mul_le_mul_left _ h
    _ = _ := by rw [← ha]; ring

end RowColumn.WordOrbits

namespace RowColumn.WordOrbits
open scoped BigOperators Classical Nat
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma typeMass_le_mode (a : S → A) (q : A → Fin (Fintype.card S + 1)) :
    typeMass a q ≤ typeMass a (counts a) := by
  by_cases hn : Nonempty {w : S → A // counts w = q}
  · obtain ⟨w,hw⟩ := hn
    rw [← hw]
    exact empirical_type_mode a w
  · let : IsEmpty {w : S → A // counts w = q} := not_nonempty_iff.mp hn
    simp [typeMass]

lemma sum_typeMass (a : S → A) :
    (∑ q : A → Fin (Fintype.card S+1), typeMass a q) =
      (Fintype.card S)^(Fintype.card S) := by
  have he (q : A → Fin (Fintype.card S+1)) : typeMass a q =
      ∑ w : {w : S → A // counts w = q}, ∏ x : S, (counts a (w.1 x)).val := by
    have hh (w : {w : S → A // counts w = q}) :
        (∏ x : S, (counts a (w.1 x)).val) = ∏ c : A, (counts a c).val ^ (q c).val := by
      rw [prod_by_counts w.1 (fun c => (counts a c).val), w.2]
    simp only [hh, Finset.sum_const, Finset.card_univ, smul_eq_mul, typeMass]
  simp_rw [he]
  rw [Fintype.sum_fiberwise counts (fun w : S → A => ∏ x : S, (counts a (w x)).val),
    ← Fintype.prod_sum (fun (_ : S) (c : A) => (counts a c).val)]
  simp only [sum_counts, Finset.prod_const, Finset.card_univ]

/-- Elementary finite postselection mass bound: an empirical type has at
least the inverse number of possible occupation tables. -/
lemma empirical_mass_lower (a : S → A) :
    (Fintype.card S)^(Fintype.card S) ≤
      (Fintype.card S+1)^(Fintype.card A) * typeMass a (counts a) := by
  rw [← sum_typeMass a]
  have hh := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => typeMass_le_mode a q)
  simpa using hh

end RowColumn.WordOrbits

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] [Fintype A] in
lemma normSq_empiricalAmplitude (a : S → A) (c : A) :
    Complex.normSq (empiricalAmplitude a c) =
      (counts a c).val / (Fintype.card S : ℝ) := by
  simp only [empiricalAmplitude, Complex.normSq_ofReal]
  exact Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [DecidableEq S] in
lemma empiricalAmplitude_normalized (a : S → A) (hn : 0 < Fintype.card S) :
    (∑ c : A, Complex.normSq (empiricalAmplitude a c)) = 1 := by
  simp only [normSq_empiricalAmplitude, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_counts]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hn)

omit [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma normSq_tensorVector (z : A → ℂ) (w : S → A) :
    Complex.normSq (tensorVector z w) = ∏ x : S, Complex.normSq (z (w x)) := by
  exact map_prod Complex.normSq _ _

omit [DecidableEq S] in
lemma normSq_empirical_tensor (a : S → A) :
    Complex.normSq (tensorVector (empiricalAmplitude a) a) =
      (∏ c : A, ((counts a c).val : ℝ)^(counts a c).val) /
        (Fintype.card S : ℝ)^(Fintype.card S) := by
  rw [normSq_tensorVector]
  simp_rw [normSq_empiricalAmplitude]
  rw [Finset.prod_div_distrib, prod_by_counts a (fun c => ((counts a c).val : ℝ))]
  simp

lemma empirical_type_probability (a : S → A) (hn : 0 < Fintype.card S) :
    1 ≤ ((Fintype.card S+1)^(Fintype.card A) : ℕ) *
      ((Fintype.card {w : S → A // counts w = counts a} : ℝ) *
        Complex.normSq (tensorVector (empiricalAmplitude a) a)) := by
  have hh := empirical_mass_lower a
  rw [normSq_empirical_tensor]
  have hden : 0 < (Fintype.card S : ℝ)^Fintype.card S := by positivity
  rw [← mul_div_assoc, ← mul_div_assoc, le_div_iff₀ hden, one_mul]
  dsimp only [typeMass] at hh
  exact_mod_cast hh

end RowColumn.Postselection


noncomputable section
open scoped BigOperators Classical
namespace RowColumn.Postselection
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

/-- Finite exact phase integration: order n+1 resolves every occupation
vector with entries in 0,...,n, with no analytical Haar integral. -/
lemma phase_parseval (f : CountIndex A n → ℂ) :
    (∑ θ : Phases A n, Complex.normSq (∑ q, countCharacter q θ * f q)) =
      (Fintype.card (Phases A n) : ℝ) * ∑ q, Complex.normSq (f q) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj, map_sum, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  have he (θ : Phases A n) (q r : CountIndex A n) :
      (countCharacter q θ * f q) * ((starRingEnd ℂ) (countCharacter r θ) *
        (starRingEnd ℂ) (f r)) =
      (countCharacter q θ * (starRingEnd ℂ) (countCharacter r θ)) *
        (f q * (starRingEnd ℂ) (f r)) := by ring
  simp_rw [he]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, character_orthogonality]
  simp [ite_mul]

lemma phase_single_bound (f : CountIndex A n → ℂ) (q : CountIndex A n) :
    (Fintype.card (Phases A n) : ℝ) * Complex.normSq (f q) ≤
      ∑ θ : Phases A n, Complex.normSq (∑ r, countCharacter r θ * f r) := by
  rw [phase_parseval]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ q)

end RowColumn.Postselection
namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits

lemma normSq_sum_mul_le {I : Type*} [Fintype I] (v x : I → ℂ) :
    Complex.normSq (∑ i, v i * x i) ≤
      (∑ i, Complex.normSq (v i)) * ∑ i, Complex.normSq (x i) := by
  have hh : ‖∑ i, v i * x i‖ ≤ ∑ i, ‖v i‖ * ‖x i‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => v i * x i)
  calc
    Complex.normSq (∑ i, v i * x i) = ‖∑ i, v i * x i‖^2 := (Complex.sq_norm _).symm
    _ ≤ (∑ i, ‖v i‖ * ‖x i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ ≤ (∑ i, ‖v i‖^2) * ∑ i, ‖x i‖^2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by simp only [Complex.sq_norm]

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] [Fintype A] in
lemma representative_counts (a₀ : S → A) (q : Types (S := S) (A := A))
    (h : Nonempty {w : S → A // counts w = q}) :
    counts (typeRepresentative a₀ q) = q := by
  simp only [typeRepresentative, dite_eq_left h]
  exact h.some.2

lemma typeAverage_pair (v x : (S → A) → ℂ)
    (hv : ∀ a b, counts a = counts b → v a = v b) :
    (∑ w : S → A, v w * typeAverage x w) = ∑ w : S → A, v w * x w := by
  rw [← Fintype.sum_fiberwise counts (fun w : S → A => v w * typeAverage x w),
    ← Fintype.sum_fiberwise counts (fun w : S → A => v w * x w)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hn : Nonempty {w : S → A // counts w = q}
  · obtain ⟨a,ha⟩ := hn
    have hc : (typeSize q : ℂ) ≠ 0 := by
      have hn : 0 < typeSize q := Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩
      exact_mod_cast Nat.ne_of_gt hn
    have he (w : {w : S → A // counts w = q}) : v w.1 = v a := hv _ _ (w.2.trans ha.symm)
    simp only [typeAverage, he,
      show ∀ w : {w : S → A // counts w = q}, counts w.1 = q from fun w => w.2]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    change (typeSize q : ℂ) * (v a * (typeSum x q / typeSize q)) = v a * typeSum x q
    field_simp
  · let : IsEmpty {w : S → A // counts w = q} := not_nonempty_iff.mp hn
    simp

lemma typeAverage_normSq (x : (S → A) → ℂ) :
    (∑ w : S → A, Complex.normSq (typeAverage x w)) =
      ∑ q : Types (S := S) (A := A), Complex.normSq (typeSum x q) / typeSize q := by
  rw [← Fintype.sum_fiberwise counts (fun w : S → A => Complex.normSq (typeAverage x w))]
  apply Finset.sum_congr rfl
  intro q _
  simp only [typeAverage,
    show ∀ w : {w : S → A // counts w = q}, counts w.1 = q from fun w => w.2,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (typeSize q : ℝ) * Complex.normSq (typeSum x q / (typeSize q : ℂ)) = _
  rw [Complex.normSq_div]
  have he : Complex.normSq (typeSize q : ℂ) = (typeSize q : ℝ)^2 := by simp [Complex.normSq_apply]; ring
  rw [he]
  by_cases hh : typeSize q = 0
  · simp [hh]
  · have hc : (typeSize q : ℝ) ≠ 0 := by exact_mod_cast hh
    field_simp

lemma invariant_vector_bound (v x : (S → A) → ℂ)
    (hv : ∀ a b, counts a = counts b → v a = v b) :
    Complex.normSq (∑ w, v w * x w) ≤
      (∑ w, Complex.normSq (v w)) *
        ∑ q : Types (S := S) (A := A), Complex.normSq (typeSum x q) / typeSize q := by
  rw [← typeAverage_pair v x hv, ← typeAverage_normSq]
  exact normSq_sum_mul_le v (typeAverage x)

end RowColumn.Postselection

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] in
lemma tensorVector_by_counts (z : A → ℂ) (w : S → A) :
    tensorVector z w = typeAmplitude z (counts w) := prod_by_counts w z

omit [DecidableEq S] in
lemma twistedAmplitude_normalized (a : S → A) (hn : 0 < Fintype.card S)
    (θ : Phases A (Fintype.card S)) :
    (∑ c : A, Complex.normSq (twistedAmplitude a θ c)) = 1 := by
  have hc (c : A) : Complex.normSq (ZMod.stdAddChar (θ c)) = 1 := by
    rw [← Complex.sq_norm, AddChar.norm_apply]; norm_num
  simp only [twistedAmplitude, Complex.normSq_mul, hc, mul_one]
  exact empiricalAmplitude_normalized a hn

omit [DecidableEq S] in
lemma tensorVector_twisted (a w : S → A) (θ : Phases A (Fintype.card S)) :
    tensorVector (twistedAmplitude a θ) w =
      countCharacter (counts w) θ * typeAmplitude (empiricalAmplitude a) (counts w) := by
  change (∏ x : S, empiricalAmplitude a (w x) * ZMod.stdAddChar (θ (w x))) = _
  rw [Finset.prod_mul_distrib, prod_by_counts w (empiricalAmplitude a),
    prod_by_counts w (fun c => ZMod.stdAddChar (θ c)), ← countCharacter_eq_prod]
  exact mul_comm _ _

lemma twisted_pair (a : S → A) (θ : Phases A (Fintype.card S)) (x : (S → A) → ℂ) :
    (∑ w, tensorVector (twistedAmplitude a θ) w * x w) =
      ∑ q : Types (S := S) (A := A),
        countCharacter q θ * (typeAmplitude (empiricalAmplitude a) q * typeSum x q) := by
  simp_rw [tensorVector_twisted]
  rw [← Fintype.sum_fiberwise counts (fun w : S → A =>
    countCharacter (counts w) θ * typeAmplitude (empiricalAmplitude a) (counts w) * x w)]
  apply Finset.sum_congr rfl
  intro q _
  simp only [show ∀ w : {w : S → A // counts w = q}, counts w.1 = q from fun w => w.2]
  rw [← Finset.mul_sum]
  exact mul_assoc _ _ _

lemma type_phase_bound (a : S → A) (x : (S → A) → ℂ) :
    (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      (Complex.normSq (tensorVector (empiricalAmplitude a) a) *
        Complex.normSq (typeSum x (counts a))) ≤
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w, tensorVector (twistedAmplitude a θ) w * x w) := by
  simp_rw [twisted_pair]
  have hh := phase_single_bound (fun q : Types (S := S) (A := A) =>
    typeAmplitude (empiricalAmplitude a) q * typeSum x q) (counts a)
  simpa only [Complex.normSq_mul, tensorVector_by_counts] using hh

lemma type_representative_bound (a₀ : S → A) (hn : 0 < Fintype.card S)
    (x : (S → A) → ℂ) (q : Types (S := S) (A := A)) :
    Complex.normSq (typeSum x q) / typeSize q ≤
      ((Fintype.card S+1)^(Fintype.card A) : ℕ) /
        (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w, tensorVector (twistedAmplitude (typeRepresentative a₀ q) θ) w * x w) := by
  by_cases he : Nonempty {w : S → A // counts w = q}
  · let a := typeRepresentative a₀ q
    have ha : counts a = q := representative_counts a₀ q he
    have hp := empirical_type_probability a hn
    have ht := type_phase_bound a x
    rw [ha] at ht
    change 1 ≤ ((Fintype.card S+1)^(Fintype.card A) : ℕ) *
      ((typeSize (counts a) : ℝ) * Complex.normSq (tensorVector (empiricalAmplitude a) a)) at hp
    rw [ha] at hp
    have hq : (0 : ℝ) < typeSize q := by
      exact_mod_cast Fintype.card_pos_iff.mpr he
    have hP : (0 : ℝ) < Fintype.card (Phases A (Fintype.card S)) := by
      exact_mod_cast Fintype.card_pos
    have ha0 := Complex.normSq_nonneg (tensorVector (empiricalAmplitude a) a)
    have hx0 := Complex.normSq_nonneg (typeSum x q)
    have hD0 : (0 : ℝ) ≤ ((Fintype.card S+1)^(Fintype.card A) : ℕ) := Nat.cast_nonneg _
    rw [div_le_iff₀ hq]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hP]
    nlinarith [mul_le_mul_of_nonneg_right hp hx0,
      mul_le_mul_of_nonneg_left ht (mul_nonneg hD0 (le_of_lt hq))]
  · let : IsEmpty {w : S → A // counts w = q} := not_nonempty_iff.mp he
    have hx : typeSum x q = 0 := by simp [typeSum]
    rw [hx, Complex.normSq_zero, zero_div]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

/-- Exact finite symmetric-vector postselection, with a polynomial cost
in the slot number and alphabet size. Every mixture vector is a normalized
identical-slot tensor power; the construction is explicit and finite. -/
theorem symmetric_postselection (a₀ : S → A) (hn : 0 < Fintype.card S)
    (v x : (S → A) → ℂ) (hv : ∀ a b, counts a = counts b → v a = v b) :
    Complex.normSq (∑ w, v w * x w) ≤
      (∑ w, Complex.normSq (v w)) *
      (((Fintype.card S+1)^(Fintype.card A) : ℕ) /
        (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := A),
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w, tensorVector (twistedAmplitude (typeRepresentative a₀ q) θ) w * x w)) := by
  apply (invariant_vector_bound v x hv).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun q _ => type_representative_bound a₀ hn x q)

end RowColumn.Postselection

namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma tensorVector_truncate (good : A → Prop) [DecidablePred good]
    (z : A → ℂ) (w : S → A) :
    tensorVector (truncateAmplitude good z) w =
      if ∀ i, good (w i) then tensorVector z w else 0 := by
  by_cases h : ∀ i, good (w i)
  · simp [tensorVector, truncateAmplitude, h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [truncateAmplitude, hi])

omit [DecidableEq S] in
lemma truncated_twisted_subnormalized (good : A → Prop) [DecidablePred good]
    (a : S → A) (hn : 0 < Fintype.card S) (θ : Phases A (Fintype.card S)) :
    (∑ c, Complex.normSq (truncateAmplitude good (twistedAmplitude a θ) c)) ≤ 1 := by
  rw [← twistedAmplitude_normalized a hn θ]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : good c
  · simp [truncateAmplitude, hc]
  · simpa [truncateAmplitude, hc] using Complex.normSq_nonneg (twistedAmplitude a θ c)

/-- Symmetric postselection retaining a prescribed alphabet support. In the
application good(c,e) means that the physical and auxiliary parities agree,
so the resulting Gram states are block diagonal. -/
theorem supported_symmetric_postselection (a₀ : S → A) (hn : 0 < Fintype.card S)
    (good : A → Prop) [DecidablePred good] (v x : (S → A) → ℂ)
    (hv : ∀ a b, counts a = counts b → v a = v b)
    (hsupp : ∀ w, ¬ (∀ i, good (w i)) → v w = 0) :
    Complex.normSq (∑ w, v w * x w) ≤
      (∑ w, Complex.normSq (v w)) *
      (((Fintype.card S+1)^(Fintype.card A) : ℕ) /
        (Fintype.card (Phases A (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := A),
      ∑ θ : Phases A (Fintype.card S),
        Complex.normSq (∑ w,
          tensorVector (truncateAmplitude good (twistedAmplitude (typeRepresentative a₀ q) θ)) w * x w)) := by
  let y : (S → A) → ℂ := fun w => if ∀ i, good (w i) then x w else 0
  have he (w : S → A) : v w * y w = v w * x w := by
    by_cases hw : ∀ i, good (w i)
    · simp [y, hw]
    · simp [y, hw, hsupp w hw]
  have ht (z : A → ℂ) (w : S → A) :
      tensorVector z w * y w = tensorVector (truncateAmplitude good z) w * x w := by
    rw [tensorVector_truncate]
    by_cases hw : ∀ i, good (w i) <;> simp [y, hw]
  have hh := symmetric_postselection a₀ hn v y hv
  simpa only [he, ht] using hh

end RowColumn.Postselection
namespace RowColumn.Postselection
open scoped BigOperators Classical
open WordOrbits
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

lemma purification_pair (B : (S → C) → (S → C) → ℂ) (x : (S → C) → ℂ) (v : S → C) :
    (∑ a : S → C × C, purificationVector B a * purificationTest x v a) =
      ∑ w : S → C, B w v * x w := by
  calc
    _ = ∑ p : (S → C) × (S → C), B p.1 p.2 * (if p.2 = v then x p.1 else 0) :=
      Fintype.sum_equiv pairWordsEquiv _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp [mul_ite]

omit [DecidableEq C] in
lemma purification_normSq (B : (S → C) → (S → C) → ℂ) :
    (∑ a : S → C × C, Complex.normSq (purificationVector B a)) = purifierTrace B := by
  calc
    _ = ∑ p : (S → C) × (S → C), Complex.normSq (B p.1 p.2) :=
      Fintype.sum_equiv pairWordsEquiv _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

end RowColumn.Postselection

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I]

lemma commute_perm_iff (A : Matrix I I ℂ) (p : Equiv.Perm I) :
    Commute A (p.permMatrix ℂ) ↔ ∀ i j, A (p i) (p j) = A i j := by
  change A * p.permMatrix ℂ = p.permMatrix ℂ * A ↔ _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  constructor
  · intro h i j
    have hh := congrArg (fun M : Matrix I I ℂ => M i (p j)) h
    simpa using hh.symm
  · intro h
    ext i j
    exact (h i (p.symm j)).symm.trans (by simp)

lemma sqrt_permutation_invariant (A : Matrix I I ℂ) (hA : A.PosSemidef)
    (p : Equiv.Perm I) (h : ∀ i j, A (p i) (p j) = A i j) :
    ∀ i j, CFC.sqrt A (p i) (p j) = CFC.sqrt A i j :=
  (commute_perm_iff _ p).mp (sqrt_commute A _ hA ((commute_perm_iff A p).mpr h))

lemma normSq_eq_re (z : ℂ) : Complex.normSq z = (z * star z).re := by
  rw [Complex.star_def, Complex.mul_conj]
  rfl

omit [DecidableEq I] in
lemma factorQuadratic_eq (B : Matrix I I ℂ) (x : I → ℂ) :
    factorQuadratic B x = quadratic (B * B.conjTranspose) x := by
  simp only [factorQuadratic, quadratic, Matrix.mul_apply, Matrix.conjTranspose_apply,
    normSq_eq_re, star_sum, star_mul, Complex.re_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  ring

lemma sqrt_factorQuadratic (A : Matrix I I ℂ) (hA : A.PosSemidef) (x : I → ℂ) :
    factorQuadratic (CFC.sqrt A) x = quadratic A x := by
  rw [factorQuadratic_eq, (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq,
    CFC.sqrt_mul_sqrt_self A hA.nonneg]

lemma sqrt_trace (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    (∑ w, ∑ v, Complex.normSq (CFC.sqrt A w v)) = A.trace.re := by
  have hs : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have he : CFC.sqrt A * (CFC.sqrt A).conjTranspose = A := by
    rw [hs, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  conv_rhs => rw [← he]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  exact normSq_eq_re _

end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

lemma tensorMatrix_posSemidef (A : S → Matrix C C ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensorMatrix A).PosSemidef := by
  let B := fun i => CFC.sqrt (A i)
  have hb (i : S) : (B i).conjTranspose * B i = A i := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A i))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ (hA i).nonneg
  have he : (tensorMatrix B).conjTranspose * tensorMatrix B = tensorMatrix A := by
    rw [tensorMatrix_star, tensorMatrix_mul]
    simp_rw [hb]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq C] in
lemma gramState_posSemidef (z : C × C → ℂ) : (gramState z).PosSemidef := by
  have hh := Matrix.posSemidef_conjTranspose_mul_self
    (letterMatrix z).conjTranspose
  simpa only [Matrix.conjTranspose_conjTranspose, gramState] using hh

omit [DecidableEq C] in
lemma gramState_trace (z : C × C → ℂ) :
    (gramState z).trace.re = ∑ p : C × C, Complex.normSq (z p) := by
  rw [Fintype.sum_prod_type]
  simp only [gramState, letterMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [Complex.star_def, Complex.mul_conj]
  rfl

omit [DecidableEq C] in
lemma gramState_parity_supported (odd : C → Prop) [DecidablePred odd]
    (z : C × C → ℂ) (hz : ∀ c d, ¬ (odd c ↔ odd d) → z (c,d) = 0)
    (c d : C) (hc : ¬ (odd c ↔ odd d)) : gramState z c d = 0 := by
  simp only [gramState, Matrix.mul_apply, letterMatrix, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : odd c ↔ odd e
  · have hd : ¬ (odd d ↔ odd e) := fun h => hc (he.trans h.symm)
    simp [hz d e hd]
  · simp [hz c e he]

end RowColumn.MatrixState

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Sectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace RowColumn.Signed
open scoped Classical
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] in
lemma frame_pred_congr (p q : S → Prop) [dp : DecidablePred p] [dq : DecidablePred q]
    (hp : Fintype.card {x : S // p x} = k)
    (hq : Fintype.card {x : S // q x} = k)
    (he : p = q) (x : S) (hx : p x) (hy : q x) :
    Fintype.equivFinOfCardEq hp ⟨x,hx⟩ = Fintype.equivFinOfCardEq hq ⟨x,hy⟩ := by
  subst q
  have hd : dq = dp := Subsingleton.elim _ _
  subst dq
  rfl

omit [Fintype C] [DecidableEq C] in
omit [DecidableEq S] in
lemma oddFrame_parity_congr (w v : Words (S := S) odd k)
    (hp : ∀ x, odd (w.1 x) ↔ odd (v.1 x)) (x : S)
    (hx : odd (w.1 x)) (hv : odd (v.1 x)) :
    oddFrame w ⟨x,hx⟩ = oddFrame v ⟨x,hv⟩ := by
  exact frame_pred_congr _ _ w.2 v.2 (funext fun x => propext (hp x)) x hx hv

omit [Fintype C] [DecidableEq C] [DecidableEq S] in
lemma oddPerm_parity_congr (g : Equiv.Perm S) (w v : Words (S := S) odd k)
    (hp : ∀ x, odd (w.1 x) ↔ odd (v.1 x)) : oddPerm g w = oddPerm g v := by
  apply Equiv.ext
  intro i
  have he : ((oddFrame w).symm i).val = ((oddFrame v).symm i).val := by
    have hh := oddFrame_parity_congr w v hp ((oddFrame w).symm i).val
      ((oddFrame w).symm i).property ((hp _).mp ((oddFrame w).symm i).property)
    rw [Equiv.apply_symm_apply] at hh
    have ht := congrArg (fun z => ((oddFrame v).symm z).val) hh
    simpa using ht.symm
  have ha : ∀ x, odd ((actWord g w).1 x) ↔ odd ((actWord g v).1 x) := fun x => hp _
  change oddFrame (actWord g w) ⟨g ((oddFrame w).symm i).val, _⟩ =
    oddFrame (actWord g v) ⟨g ((oddFrame v).symm i).val, _⟩
  have hw : odd ((actWord g w).1 (g ((oddFrame w).symm i).val)) := by
    simpa using ((oddFrame w).symm i).property
  calc
    _ = oddFrame (actWord g v) ⟨g ((oddFrame w).symm i).val, (ha _).mp hw⟩ :=
      oddFrame_parity_congr _ _ ha _ _ _
    _ = _ := congrArg (oddFrame (actWord g v)) (Subtype.ext (congrArg g he))
end RowColumn.Signed

end
end
end

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator
namespace RowColumn.MatrixState
open Signed FiniteStarAlgebra
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ)

lemma matrix_wordVector (M : Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ)
    (w v : Words (S := S) odd k) :
    Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ) M (wordVector v) w = M w v := by
  change (∑ z, M w z * (if z=v then 1 else 0)) = M w v
  simp

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_TensorFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

lemma sectorTensor_positive (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (sectorTensor odd k M).PosSemidef :=
  (tensorMatrix_posSemidef M hM).submatrix _

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma algebraMatrix_star (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) : algebraMatrix A (star a) = star (algebraMatrix A a) :=
  (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).symm.map_star' a.val
lemma algebraMatrix_hermitian (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) (ha : star a=a) : (algebraMatrix A a).IsHermitian := by
  change star (algebraMatrix A a)=_
  rw [← algebraMatrix_star, ha]

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_LineStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn.Postselection
open WordOrbits
variable {S L A : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]

omit [DecidableEq S] [Fintype L] in
lemma allocationPerm_spec (line b : S → L) (hb : counts b = counts line) (i : S) :
    b (allocationPerm line b hb i) = line i :=
  (same_counts_permutation line b hb.symm).choose_spec i

omit [DecidableEq S] [Fintype A] in
lemma counts_precomp (w : S → A) (p : Equiv.Perm S) : counts (w ∘ p) = counts w := by
  funext c
  apply Fin.ext
  exact Fintype.card_congr
    { toFun := fun i => ⟨p i.1,i.2⟩
      invFun := fun i => ⟨p.symm i.1,by simpa using i.2⟩
      left_inv := by intro i; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }

omit [Fintype A] [DecidableEq A] in
omit [DecidableEq S] in
lemma symExtension_on_line (line : S → L) (v : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i) = line i) → ∀ w, v (w ∘ p) = v w)
    (w : S → A) : symExtension line v (fun i => (line i,w i)) = v w := by
  simp only [symExtension]
  exact hv (allocationPerm line line rfl) (allocationPerm_spec line line rfl) w

omit [Fintype A] [DecidableEq A] in
omit [DecidableEq S] in
lemma symExtension_invariant (line : S → L) (v : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i) = line i) → ∀ w, v (w ∘ p) = v w)
    (p : Equiv.Perm S) (w : S → L × A) : symExtension line v (w ∘ p) = symExtension line v w := by
  have hc : counts (fun i => (w (p i)).1) = counts (fun i => (w i).1) := counts_precomp (fun i => (w i).1) p
  by_cases hb : counts (fun i => (w i).1) = counts line
  · have hb' : counts (fun i => (w (p i)).1) = counts line := hc.trans hb
    simp only [symExtension, Function.comp_apply, dite_eq_left hb, dite_eq_left hb']
    let e := allocationPerm line (fun i => (w i).1) hb
    let e' := allocationPerm line (fun i => (w (p i)).1) hb'
    let q : Equiv.Perm S := e'.trans (p.trans e.symm)
    have hq (i : S) : line (q i) = line i := by
      rw [← allocationPerm_spec line (fun i => (w i).1) hb (q i)]
      change (w (e (e.symm (p (e' i))))).1 = line i
      rw [Equiv.apply_symm_apply]
      exact allocationPerm_spec line (fun i => (w (p i)).1) hb' i
    have hh := hv q hq (fun i => (w (e i)).2)
    change v (fun i => (w (p (e' i))).2) = v (fun i => (w (e i)).2)
    convert hh using 1
    congr 1
    ext i
    simp only [q, Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply]
  · have hb' : ¬ counts (fun i => (w (p i)).1) = counts line := fun hh => hb (hc.symm.trans hh)
    simp only [symExtension, Function.comp_apply, dite_eq_right hb, dite_eq_right hb']

omit [Fintype A] in
omit [DecidableEq S] in
lemma symExtension_counts (line : S → L) (v : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i) = line i) → ∀ w, v (w ∘ p) = v w)
    (w z : S → L × A) (he : counts w = counts z) : symExtension line v w = symExtension line v z := by
  obtain ⟨p,hp⟩ := same_counts_permutation w z he
  have hh : z ∘ p = w := funext hp
  rw [← hh]
  exact symExtension_invariant line v hv p z

omit [DecidableEq A] in
lemma symExtension_norm (line : S → L) (v : (S → A) → ℂ) :
    (∑ w : S → L × A, Complex.normSq (symExtension line v w)) =
      (Fintype.card (Allocations line) : ℝ) * ∑ w : S → A, Complex.normSq (v w) := by
  rw [← (labelWordEquiv (S := S) (L := L) (A := A)).symm.sum_comp,
    Fintype.sum_prod_type]
  change (∑ b : S → L, ∑ w : S → A, Complex.normSq
    (if hb : counts b=counts line then v (w ∘ allocationPerm line b hb) else 0)) = _
  have he (b : S → L) : (∑ w : S → A, Complex.normSq
      (if hb : counts b=counts line then v (w ∘ allocationPerm line b hb) else 0)) =
        if counts b=counts line then ∑ w : S → A, Complex.normSq (v w) else 0 := by
    split_ifs with hb
    · exact Equiv.sum_comp (precompWordEquiv (A := A) (allocationPerm line b hb)) (fun w => Complex.normSq (v w))
    · simp
  simp_rw [he]
  simp [Finset.sum_ite, Fintype.card_subtype, Allocations]


omit [DecidableEq A] in
lemma labeled_pair (line : S → L) (x : (S → A) → ℂ) (f : (S → L × A) → ℂ) :
    (∑ w, f w * labelTest line x w) = ∑ w : S → A, f (fun i => (line i,w i)) * x w := by
  rw [← (labelWordEquiv (S := S) (L := L) (A := A)).symm.sum_comp,
    Fintype.sum_prod_type]
  change (∑ b : S → L, ∑ w : S → A, f (fun i => (b i,w i)) *
    (if b=line then x w else 0)) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp

lemma allocation_probability (line : S → L) (r : L → ℝ)
    (hr : ∀ l, 0 ≤ r l) (hs : ∑ l, r l ≤ 1) :
    (Fintype.card (Allocations line) : ℝ) * (∏ i, r (line i)) ≤ 1 := by
  have he (b : S → L) (hb : counts b=counts line) :
      (∏ i, r (b i)) = ∏ i, r (line i) := by
    rw [prod_by_counts, prod_by_counts, hb]
  have hh : (∑ b : S → L, if counts b=counts line then ∏ i, r (line i) else 0) ≤
      ∑ b : S → L, ∏ i, r (b i) := by
    apply Finset.sum_le_sum
    intro b _
    split_ifs with hb
    · exact le_of_eq (he b hb).symm
    · exact Finset.prod_nonneg (fun _ _ => hr _)
  have hl : (∑ b : S → L, if counts b=counts line then ∏ i, r (line i) else 0) =
      (Fintype.card (Allocations line) : ℝ) * (∏ i, r (line i)) := by
    simp [Finset.sum_ite, Fintype.card_subtype, Allocations]
  rw [hl, ← Fintype.prod_sum] at hh
  exact hh.trans (Finset.prod_le_one (fun _ _ => Finset.sum_nonneg (fun l _ => hr l)) (fun _ _ => hs))

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma lineMass_nonneg (z : L × A → ℂ) (l : L) : 0 ≤ lineMass z l :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma lineMass_zero (z : L × A → ℂ) (l : L) (h : lineMass z l=0) (a : A) : z (l,a)=0 := by
  apply Complex.normSq_eq_zero.mp
  have hh : Complex.normSq (z (l,a)) ≤ lineMass z l :=
    Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (z (l,b))) (Finset.mem_univ a)
  exact le_antisymm (h ▸ hh) (Complex.normSq_nonneg _)

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma line_reconstruction (z : L × A → ℂ) (l : L) (a : A) :
    z (l,a) = (Real.sqrt (lineMass z l) : ℂ) * normalizedLine z l a := by
  by_cases hz : lineMass z l=0
  · simp [normalizedLine, hz, lineMass_zero z l hz a]
  · have h : (Real.sqrt (lineMass z l) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (lineMass_nonneg z l) (Ne.symm hz)))
    simp [normalizedLine, h]

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma normalizedLine_norm (z : L × A → ℂ) (l : L) :
    (∑ a, Complex.normSq (normalizedLine z l a)) ≤ 1 := by
  by_cases hz : lineMass z l=0
  · simp [normalizedLine, hz]
  · have hp : 0 < lineMass z l := lt_of_le_of_ne (lineMass_nonneg z l) (Ne.symm hz)
    simp_rw [normalizedLine, map_mul, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hp)]
    rw [← Finset.mul_sum]
    change (lineMass z l)⁻¹ * lineMass z l ≤ 1
    rw [inv_mul_cancel₀ hz]

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma labeled_tensor_pair (line : S → L) (z : L × A → ℂ) (x : (S → A) → ℂ) :
    Complex.normSq (∑ w : S → A, tensorVector z (fun i => (line i,w i)) * x w) =
      (∏ i, lineMass z (line i)) *
        Complex.normSq (∑ w : S → A, (∏ i, normalizedLine z (line i) (w i)) * x w) := by
  have he (w : S → A) : tensorVector z (fun i => (line i,w i)) =
      (∏ i, (Real.sqrt (lineMass z (line i)) : ℂ)) * ∏ i, normalizedLine z (line i) (w i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => line_reconstruction z (line i) (w i))
  simp_rw [he, mul_assoc]
  rw [← Finset.mul_sum, map_mul]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (Complex.normSq_ofReal _).trans (Real.mul_self_sqrt (lineMass_nonneg z (line i)))


omit [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma symExtension_supported (line : S → L) (v : (S → A) → ℂ)
    (good : A → Prop) [DecidablePred good]
    (hv : ∀ w, ¬ (∀ i, good (w i)) → v w=0)
    (w : S → L × A) (hw : ¬ ∀ i, good (w i).2) : symExtension line v w=0 := by
  unfold symExtension
  split_ifs with hb
  · apply hv
    intro h
    apply hw
    intro i
    simpa using h ((allocationPerm line _ hb).symm i)
  · rfl

omit [DecidableEq S] in
omit [Fintype L] in
lemma lineAmplitude_norm (line : S → L) (a₀ : S → A) (good : A → Prop) [DecidablePred good]
    (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) (l : L) :
    (∑ a, Complex.normSq (lineAmplitude line a₀ good q θ l a)) ≤ 1 :=
  normalizedLine_norm _ _

omit [DecidableEq S] [Fintype L] in
lemma lineAmplitude_support (line : S → L) (a₀ : S → A) (good : A → Prop) [DecidablePred good]
    (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) (l : L) (a : A)
    (ha : ¬ good a) : lineAmplitude line a₀ good q θ l a=0 := by
  simp [lineAmplitude, normalizedLine, truncateAmplitude, ha]

/-- Independent fibre postselection, with the allocation factorial cancelled
by the exact multinomial probability rather than included in the overhead. -/
theorem line_symmetric_postselection (line : S → L) (a₀ : S → A) (hn : 0 < Fintype.card S)
    (good : A → Prop) [DecidablePred good] (v x : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i)=line i) → ∀ w, v (w ∘ p)=v w)
    (hsupp : ∀ w, ¬ (∀ i, good (w i)) → v w=0) :
    Complex.normSq (∑ w, v w*x w) ≤
      (∑ w, Complex.normSq (v w)) *
      (((Fintype.card S+1)^(Fintype.card (L × A)) : ℕ) /
        (Fintype.card (Phases (L × A) (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := L × A), ∑ θ : Phases (L × A) (Fintype.card S),
        Complex.normSq (∑ w : S → A, (∏ i, lineAmplitude line a₀ good q θ (line i) (w i)) * x w)) := by
  let z (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) :=
    truncateAmplitude (fun c : L × A => good c.2)
      (twistedAmplitude (typeRepresentative (fun i => (line i,a₀ i)) q) θ)
  let R (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) :=
    Complex.normSq (∑ w : S → A, (∏ i, normalizedLine (z q θ) (line i) (w i)) * x w)
  have hz (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) :
      (Fintype.card (Allocations line) : ℝ) * (∏ i, lineMass (z q θ) (line i)) ≤ 1 := by
    apply allocation_probability line _ (lineMass_nonneg _)
    rw [show (∑ l, lineMass (z q θ) l) = ∑ c : L × A, Complex.normSq (z q θ c) from
      (Fintype.sum_prod_type (fun c : L × A => Complex.normSq (z q θ c))).symm]
    exact truncated_twisted_subnormalized _ _ hn _
  have hh := supported_symmetric_postselection (fun i => (line i,a₀ i)) hn
    (fun c : L × A => good c.2) (symExtension line v) (labelTest line x)
    (symExtension_counts line v hv) (symExtension_supported line v good hsupp)
  rw [labeled_pair] at hh
  simp_rw [symExtension_on_line line v hv] at hh
  rw [symExtension_norm] at hh
  simp_rw [labeled_pair, labeled_tensor_pair] at hh
  let c : ℝ := ((Fintype.card S+1)^(Fintype.card (L × A)) : ℕ) /
    (Fintype.card (Phases (L × A) (Fintype.card S)) : ℝ)
  change _ ≤ ((Fintype.card (Allocations line) : ℝ) * ∑ w, Complex.normSq (v w)) *
    (c * ∑ q, ∑ θ, (∏ i, lineMass (z q θ) (line i)) * R q θ) at hh
  change _ ≤ (∑ w, Complex.normSq (v w)) * (c * ∑ q, ∑ θ, R q θ)
  apply hh.trans
  rw [show ((Fintype.card (Allocations line) : ℝ) * ∑ w, Complex.normSq (v w)) *
      (c * ∑ q, ∑ θ, (∏ i, lineMass (z q θ) (line i)) * R q θ) =
    (∑ w, Complex.normSq (v w)) * (c * ((Fintype.card (Allocations line) : ℝ) *
      ∑ q, ∑ θ, (∏ i, lineMass (z q θ) (line i)) * R q θ)) by ring]
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c)
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun θ _ =>
    (mul_le_mul_of_nonneg_right (hz q θ) (Complex.normSq_nonneg _)).trans_eq (one_mul _)))

end RowColumn.Postselection

end
end


section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator ComplexOrder MatrixOrder
namespace RowColumn.Postselection
open MatrixState WordOrbits
variable {S L C : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype C] [DecidableEq C]

omit [DecidableEq S] [Fintype L] in
lemma lineState_positive (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S)) (l : L) :
    (lineState line a₀ odd q θ l).PosSemidef := gramState_posSemidef _

omit [DecidableEq S] in
omit [Fintype L] in
lemma lineState_trace (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S)) (l : L) :
    (lineState line a₀ odd q θ l).trace.re ≤ 1 := by
  rw [lineState, gramState_trace]
  exact lineAmplitude_norm _ _ _ _ _ _

omit [DecidableEq S] [Fintype L] in
lemma lineState_even (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S))
    (l : L) (c d : C) (h : ¬ (odd c ↔ odd d)) : lineState line a₀ odd q θ l c d=0 := by
  apply gramState_parity_supported odd _ _ c d h
  exact fun c d h => lineAmplitude_support _ _ _ _ _ _ _ h

lemma variable_purification_pair (z : S → C × C → ℂ) (x : (S → C) → ℂ) (v : S → C) :
    (∑ a : S → C × C, (∏ i, z i (a i)) * purificationTest x v a) =
      ∑ w : S → C, tensorMatrix (fun i => letterMatrix (z i)) w v * x w := by
  exact purification_pair (tensorMatrix (fun i => letterMatrix (z i))) x v

lemma variable_purification_quadratic (z : S → C × C → ℂ) (x : (S → C) → ℂ) :
    (∑ v : S → C, Complex.normSq (∑ a : S → C × C,
      (∏ i, z i (a i)) * purificationTest x v a)) =
      quadratic (tensorMatrix (fun i => gramState (z i))) x := by
  simp_rw [variable_purification_pair]
  change factorQuadratic (tensorMatrix (fun i => letterMatrix (z i))) x = _
  rw [factorQuadratic_eq, tensorMatrix_star, tensorMatrix_mul]
  rfl

/-- Explicit local domination for independent row/column permutation fibres.
All mixture terms are genuine even positive identical-slot substates within
each fibre, irrespective of its size and the deletion layout. -/
theorem positive_line_postselection (line : S → L) (a₀ : S → C × C) (hn : 0 < Fintype.card S)
    (odd : C → Prop) [DecidablePred odd] (A : Matrix (S → C) (S → C) ℂ)
    (hA : A.PosSemidef)
    (hinv : ∀ (p : Equiv.Perm S), (∀ i, line (p i)=line i) → ∀ (w v : S → C),
      A (w ∘ p) (v ∘ p)=A w v)
    (hsupp : ∀ w v, ¬ (∀ i, odd (w i) ↔ odd (v i)) → A w v=0)
    (x : (S → C) → ℂ) :
    quadratic A x ≤ A.trace.re *
      (((Fintype.card S+1)^(Fintype.card (L × (C × C))) : ℕ) /
        (Fintype.card (Phases (L × (C × C)) (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := L × (C × C)),
      ∑ θ : Phases (L × (C × C)) (Fintype.card S),
        quadratic (tensorMatrix (fun i : S => lineState line a₀ odd q θ (line i))) x) := by
  let B : Matrix (S → C) (S → C) ℂ := CFC.sqrt A
  have hi (p : Equiv.Perm S) (hp : ∀ i, line (p i)=line i) (w v : S → C) :
      B (w ∘ p) (v ∘ p)=B w v :=
    sqrt_permutation_invariant A hA (reindexWord p) (hinv p hp) w v
  have hz (w v : S → C) (hh : ¬ ∀ i, odd (w i) ↔ odd (v i)) : B w v=0 := by
    apply sqrt_block_supported (fun u : S → C => fun i => odd (u i)) A hA
      (fun u v he => hsupp u v (fun ht => he (funext fun i => propext (ht i)))) w v
    intro he
    exact hh (fun i => Iff.of_eq (congrFun he i))
  have hv (p : Equiv.Perm S) (hp : ∀ i, line (p i)=line i) (w : S → C × C) :
      purificationVector B (w ∘ p)=purificationVector B w :=
    hi p hp (fun i => (w i).1) (fun i => (w i).2)
  have hs (w : S → C × C) (hw : ¬ ∀ i, odd (w i).1 ↔ odd (w i).2) : purificationVector B w=0 :=
    hz _ _ hw
  have hh (v : S → C) := line_symmetric_postselection line a₀ hn
    (fun p : C × C => odd p.1 ↔ odd p.2) (purificationVector B) (purificationTest x v) hv hs
  simp only [purification_pair B x, purification_normSq B] at hh
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hh v)
  change factorQuadratic B x ≤ _ at hsum
  have ht : purifierTrace B=A.trace.re := sqrt_trace A hA
  rw [ht] at hsum
  change factorQuadratic (CFC.sqrt A) x ≤ _ at hsum
  rw [sqrt_factorQuadratic A hA] at hsum
  apply hsum.trans_eq
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  exact variable_purification_quadratic _ x

end RowColumn.Postselection

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Dephasing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [Fintype C] [DecidableEq C] in
lemma actWord_swap_fixed (w : Words (S := S) odd k) (x y : S) (he : w.1 x = w.1 y) :
    actWord (Equiv.swap x y) w = w := by
  apply Subtype.ext
  funext z
  change w.1 ((Equiv.swap x y)⁻¹ z) = w.1 z
  rw [Equiv.swap_inv]
  by_cases hx : z = x
  · subst z; simp [he]
  by_cases hy : z = y
  · subst z; simp [he]
  · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

omit [Fintype C] [DecidableEq C] in
lemma oddPerm_swap_sign (w : Words (S := S) odd k) (x y : S)
    (hxy : x ≠ y) (he : w.1 x = w.1 y) :
    permSign (oddPerm (Equiv.swap x y) w) = if odd (w.1 x) then -1 else 1 := by
  have hw := actWord_swap_fixed w x y he
  split_ifs with ho
  · rw [oddPerm_sign_of_stabilizes _ w hw]
    · simp [permSign, Equiv.Perm.sign_swap hxy]
    · intro z hz
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; subst z; exact hz ho
      · intro h; subst z; exact hz (he ▸ ho)
  · rw [oddPerm_of_odd_fixed _ w hw]
    · simp [permSign]
    · intro z hz
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; subst z; exact ho hz
      · intro h; subst z; exact ho (he.symm ▸ hz)

end RowColumn.Signed

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
lemma shortSubsetCode_mem {q : ℕ} (t : ShortSubsets (S := S) q) (x : S) :
    (∃ i, shortSubsetCode t i = some x) ↔ x ∈ t.1 := by
  constructor
  · rintro ⟨i, hi⟩
    unfold shortSubsetCode at hi
    split_ifs at hi with hj
    · have he := Option.some.inj hi
      rw [← he]
      exact ((t.1.equivFin).symm ⟨i.1, hj⟩).2
  · intro hx
    let j := t.1.equivFin ⟨x, hx⟩
    refine ⟨⟨j.1, j.2.trans_le t.2⟩, ?_⟩
    simp only [shortSubsetCode, dite_eq_left j.2]
    exact congrArg (fun z : t.1 => some z.1) (t.1.equivFin.symm_apply_apply ⟨x, hx⟩)

omit [Fintype S] [DecidableEq S] in
lemma shortSubsetCode_injective {q : ℕ} : Function.Injective (shortSubsetCode (S := S) (q := q)) := by
  intro t u he
  apply Subtype.ext
  apply Finset.ext
  intro x
  rw [← shortSubsetCode_mem t x, ← shortSubsetCode_mem u x, he]

omit [DecidableEq S] in
lemma card_shortSubsets_le (q : ℕ) :
    Fintype.card (ShortSubsets (S := S) q) ≤ (Fintype.card S + 1)^q := by
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin] using
    Fintype.card_le_of_injective _ (shortSubsetCode_injective (S := S) (q := q))

omit [DecidableEq S] in
lemma parityNear_symm (q : ℕ) : Std.Symm (parityNear (S := S) q) := by
  constructor
  intro b c hc
  have he : parityDifference c b = parityDifference b c := by
    ext x
    simp only [parityDifference, Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
  unfold parityNear at *
  rwa [he]

omit [DecidableEq S] in
lemma parityDifference_injective (b : S → Bool) : Function.Injective (parityDifference b) := by
  intro c d he
  funext x
  have hh : (b x ≠ c x) ↔ (b x ≠ d x) := by
    have ht := Finset.ext_iff.mp he x
    simpa only [parityDifference, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  cases hbx : b x <;> cases hcx : c x <;> cases hdx : d x <;> simp_all

lemma parityNear_count (q : ℕ) (b : S → Bool) :
    (Finset.univ.filter (parityNear q b)).card ≤ (Fintype.card S + 1)^q := by
  let f : {c : S → Bool // parityNear q b c} → ShortSubsets (S := S) q :=
    fun c => ⟨parityDifference b c.1, c.2⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    exact parityDifference_injective b (congrArg Subtype.val he)
  have hh := (Fintype.card_le_of_injective f hf).trans (card_shortSubsets_le (S := S) q)
  simpa only [Fintype.card_subtype] using hh

end RowColumn
noncomputable section
open scoped BigOperators Classical
namespace RowColumn

section PositiveBanded
variable {V B : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [Fintype B] [DecidableEq B]

lemma positive_cross_bound (A : V →ₗ[ℂ] V) (hA : A.IsPositive) (x y : V) :
    2 * (inner ℂ x (A y)).re ≤ energy A x + energy A y := by
  have hp := hA.re_inner_nonneg_right (x-y)
  have hs : (inner ℂ y (A x)).re = (inner ℂ x (A y)).re := by
    rw [← hA.isSymmetric x y]
    exact inner_re_symm (𝕜 := ℂ) _ _
  change 0 ≤ (inner ℂ (x-y) (A (x-y))).re at hp
  simp only [map_sub, inner_sub_left, inner_sub_right, Complex.sub_re] at hp
  rw [hs] at hp
  dsimp only [energy]
  linarith

omit [DecidableEq B] in
/-- A positive block-banded matrix is dominated by its block diagonal times
the maximum number of nonzero block neighbours. This will be applied to
physical parity allocations, where signed symmetry supplies a polynomial bound. -/
lemma positive_banded_sum (A : V →ₗ[ℂ] V) (hA : A.IsPositive)
    (v : B → V) (R : B → B → Prop) [DecidableRel R]
    (hRs : Std.Symm R) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter (R i)).card ≤ D)
    (hz : ∀ i j, ¬ R i j → inner ℂ (v i) (A (v j)) = 0) :
    energy A (∑ i, v i) ≤ (D : ℝ) * ∑ i, energy A (v i) := by
  have hn (i : B) : 0 ≤ energy A (v i) := hA.re_inner_nonneg_right _
  have he (i j : B) : 2 * (inner ℂ (v i) (A (v j))).re ≤
      if R i j then energy A (v i) + energy A (v j) else 0 := by
    split_ifs with hr
    · exact positive_cross_bound A hA _ _
    · rw [hz i j hr]; simp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he i j))
  have hleft : (∑ i, ∑ j, 2 * (inner ℂ (v i) (A (v j))).re) =
      2 * energy A (∑ i, v i) := by
    simp only [energy, map_sum, sum_inner, inner_sum, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hleft] at hs
  have htrace : (∑ i, ∑ j, if R i j then energy A (v i) + energy A (v j) else 0) =
      2 * ∑ i, ((Finset.univ.filter (R i)).card : ℝ) * energy A (v i) := by
    have hsplit (i j : B) : (if R i j then energy A (v i) + energy A (v j) else 0) =
        (if R i j then energy A (v i) else 0) + (if R i j then energy A (v j) else 0) := by
      split_ifs <;> simp
    simp only [hsplit, Finset.sum_add_distrib]
    have hswap : (∑ i, ∑ j, if R i j then energy A (v j) else 0) =
        ∑ i, ∑ j, if R i j then energy A (v i) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hr : R j i ↔ R i j := ⟨fun h => hRs.symm _ _ h, fun h => hRs.symm _ _ h⟩
      simp only [hr]
    rw [hswap]
    have hcard (i : B) : (∑ j, if R i j then energy A (v i) else 0) =
        ((Finset.univ.filter (R i)).card : ℝ) * energy A (v i) := by
      rw [← Finset.sum_filter]
      simp
    simp only [hcard]
    ring
  rw [htrace] at hs
  have hd : (∑ i, ((Finset.univ.filter (R i)).card : ℝ) * energy A (v i)) ≤
      (D : ℝ) * ∑ i, energy A (v i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (hn i))
  linarith

end PositiveBanded
end RowColumn
namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [Fintype C] [DecidableEq C] in
lemma sum_parityMasks (v : EuclideanSpace ℂ (Words (S := S) odd k)) :
    (∑ b : S → Bool, parityMask b v) = v := by
  ext w
  simp [WithLp.ofLp_sum, parityMask]

lemma inner_wordVector (w : Words (S := S) odd k)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) : inner ℂ (wordVector w) x = x w := by
  simp [PiLp.inner_apply, wordVector, RCLike.inner_apply]

end RowColumn.Signed

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}
  (line : S → L)

omit [Fintype S] [Fintype L] [DecidableEq L] in
lemma swap_mem_lineGroup (x y : S) (hl : line x=line y) :
    Equiv.swap x y ∈ RowColumn.lineGroup line := by
  intro z
  by_cases hx : z=x
  · subst z; simp [hl]
  by_cases hy : z=y
  · subst z; simp [hl]
  · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

omit [Fintype C] [Fintype L] [DecidableEq L] in
lemma line_coefficient_zero_of_pair_repeat
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (x y : S) (hxy : x ≠ y) (hl : line x=line y)
    (hw : w.1 x = w.1 y) (hv : v.1 x = v.1 y)
    (hp : ¬ (odd (w.1 x) ↔ odd (v.1 x))) : T (wordVector v) w = 0 := by
  have he := commuting_coefficient_relation line T
    ⟨Equiv.swap x y,swap_mem_lineGroup line x y hl⟩ w v
  change permSign (oddPerm (Equiv.swap x y) v) *
      T (wordVector (actWord (Equiv.swap x y) v)) (actWord (Equiv.swap x y) w) =
    permSign (oddPerm (Equiv.swap x y) w) * T (wordVector v) w at he
  rw [actWord_swap_fixed w x y hw, actWord_swap_fixed v x y hv,
    oddPerm_swap_sign v x y hxy hv, oddPerm_swap_sign w x y hxy hw] at he
  by_cases hwo : odd (w.1 x) <;> by_cases hvo : odd (v.1 x)
  · exact (hp (iff_of_true hwo hvo)).elim
  · simp only [ite_eq_left hwo, ite_eq_right hvo, one_mul, neg_mul, one_mul] at he
    linear_combination (1/2 : ℂ) * he
  · simp only [ite_eq_right hwo, ite_eq_left hvo, one_mul, neg_mul, one_mul] at he
    linear_combination (-1/2 : ℂ) * he
  · exact (hp (iff_of_false hwo hvo)).elim

omit [Fintype C] [Fintype L] [DecidableEq L] in
lemma line_mismatch_injective
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    Function.Injective (fun x : ParityMismatch w v => (line x.1, w.1 x.1, v.1 x.1)) := by
  intro x y he
  apply Subtype.ext
  by_contra hxy
  exact hn (line_coefficient_zero_of_pair_repeat line T w v x.1 y.1 hxy
    (congrArg Prod.fst he) (congrArg (fun z => z.2.1) he)
    (congrArg (fun z => z.2.2) he) x.2)

omit [DecidableEq L] in
lemma line_parity_bandwidth
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    Fintype.card (ParityMismatch w v) ≤ Fintype.card L * Fintype.card C ^ 2 := by
  simpa only [Fintype.card_prod, pow_two] using
    Fintype.card_le_of_injective _ (line_mismatch_injective line T w v hn)

omit [DecidableEq L]

lemma line_parityNear_of_coefficient_ne_zero
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    RowColumn.parityNear (Fintype.card L * Fintype.card C ^ 2) (parityPattern w) (parityPattern v) := by
  have he : (RowColumn.parityDifference (parityPattern w) (parityPattern v)).card =
      Fintype.card (ParityMismatch w v) := by
    unfold RowColumn.parityDifference
    rw [Fintype.card_subtype]
    congr 2
    funext x
    apply propext
    simp [parityPattern]
  change (RowColumn.parityDifference (parityPattern w) (parityPattern v)).card ≤ _
  rw [he]
  exact line_parity_bandwidth line T w v hn

lemma line_parityMask_inner_zero
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (b c : S → Bool)
    (hx : ¬ RowColumn.parityNear (Fintype.card L * Fintype.card C ^ 2) b c)
    (x y : EuclideanSpace ℂ (Words (S := S) odd k)) :
    inner ℂ (parityMask b x) (T (parityMask c y)) = 0 := by
  rw [← sum_wordVectors (parityMask b x), ← sum_wordVectors (parityMask c y)]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_wordVector]
  apply Finset.sum_eq_zero
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro w _
  change (parityMask c y) v *
    ((starRingEnd ℂ) ((parityMask b x) w) * T (wordVector v) w) = 0
  by_cases hb : parityPattern w = b
  · by_cases hc : parityPattern v = c
    · have hz : T (wordVector v) w = 0 := by
        by_contra hn
        exact hx (by simpa only [hb, hc] using line_parityNear_of_coefficient_ne_zero line T w v hn)
      simp only [hz, mul_zero]
    · simp [parityMask, hc]
  · simp [parityMask, hb]

/-- Exact signed dephasing inequality. No LR or highest-weight estimate:
positivity plus the swap-forced bandwidth yields polynomial cost in the
physical parity allocation, the hard structural step for local domination. -/
theorem line_signed_parity_dephasing
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (hT : T.toLinearMap.IsPositive)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    RowColumn.energy T.toLinearMap x ≤
      ((Fintype.card S + 1) ^ (Fintype.card L * Fintype.card C ^ 2) : ℕ) *
        ∑ b : S → Bool, RowColumn.energy T.toLinearMap (parityMask b x) := by
  have hh := RowColumn.positive_banded_sum T.toLinearMap hT
    (fun b : S → Bool => parityMask b x) (RowColumn.parityNear (Fintype.card L * Fintype.card C ^ 2))
    (RowColumn.parityNear_symm _) ((Fintype.card S + 1) ^ (Fintype.card L * Fintype.card C ^ 2))
    (RowColumn.parityNear_count _) (fun b c h => line_parityMask_inner_zero line T b c h x x)
  simpa only [sum_parityMasks] using hh
end RowColumn.Signed

end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Postselection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J B : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype J] in
lemma indexInclusion_star_mul (e : J ↪ I) : (indexInclusion e).conjTranspose * indexInclusion e=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,indexInclusion,Matrix.one_apply]
  simp only [apply_ite,star_one,star_zero]
  rw [Finset.sum_eq_single (e i)]
  · simp only [ite_true,one_mul,e.injective.eq_iff]
    split_ifs <;> rfl
  · intro b _ hb
    simp [hb]
  · simp

omit [Fintype I] in
lemma extendMatrix_apply (e : J ↪ I) (A : Matrix J J ℂ) (i j : J) :
    extendMatrix e A (e i) (e j)=A i j := by
  simp only [extendMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,indexInclusion,
    apply_ite,star_one,star_zero,e.injective.eq_iff]
  simp

omit [Fintype I] [DecidableEq J] in
lemma extendMatrix_eq_zero_left (e : J ↪ I) (A : Matrix J J ℂ) (i : I) (hi : i ∉ Set.range e) (j : I) :
    extendMatrix e A i j=0 := by
  have hh : ∀ k, i≠e k := by intro k he; exact hi ⟨k,he.symm⟩
  simp [extendMatrix,Matrix.mul_apply,indexInclusion,hh]

omit [Fintype I] [DecidableEq J] in
lemma extendMatrix_eq_zero_right (e : J ↪ I) (A : Matrix J J ℂ) (i : I) (j : I) (hj : j ∉ Set.range e) :
    extendMatrix e A i j=0 := by
  have hh : ∀ k, j≠e k := by intro k he; exact hj ⟨k,he.symm⟩
  simp [extendMatrix,Matrix.mul_apply,indexInclusion,Matrix.conjTranspose_apply,hh]

omit [DecidableEq J] in
lemma extendMatrix_positive (e : J ↪ I) (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    (extendMatrix e A).PosSemidef := hA.mul_mul_conjTranspose_same _

lemma extendMatrix_trace (e : J ↪ I) (A : Matrix J J ℂ) :
    (extendMatrix e A).trace=A.trace := by
  rw [extendMatrix,Matrix.trace_mul_cycle,indexInclusion_star_mul,one_mul]

variable [Fintype B] [DecidableEq B]

omit [Fintype I] [Fintype B] in
lemma blockMask_hermitian (b : I → B) (k : B) : (blockMask b k).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  split_ifs <;> simp

lemma pinchMatrix_apply (b : I → B) (A : Matrix I I ℂ) (i j : I) :
    pinchMatrix b A i j = if b i=b j then A i j else 0 := by
  simp only [pinchMatrix,Matrix.sum_apply,blockMask,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [Finset.sum_eq_single (b i)]
  · simp only [ite_true,one_mul]
    by_cases h : b i=b j
    · simp [h]
    · simp [h,Ne.symm h]
  · intro k _ hk
    rw [ite_eq_right (Ne.symm hk),zero_mul,zero_mul]
  · simp

lemma pinchMatrix_positive (b : I → B) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    (pinchMatrix b A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply Finset.sum_nonneg
  intro k _
  have hh := hA.conjTranspose_mul_mul_same (blockMask b k)
  rw [(blockMask_hermitian b k).eq] at hh
  exact hh.nonneg

lemma pinchMatrix_trace (b : I → B) (A : Matrix I I ℂ) : (pinchMatrix b A).trace=A.trace := by
  unfold Matrix.trace Matrix.diag
  simp_rw [pinchMatrix_apply,ite_true]

lemma pinchMatrix_support (b : I → B) (A : Matrix I I ℂ) (i j : I) (h : b i ≠ b j) :
    pinchMatrix b A i j=0 := by rw [pinchMatrix_apply,ite_eq_right h]
end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma quadratic_eq_energy (A : Matrix I I ℂ) (x : I → ℂ) :
    quadratic A x = RowColumn.energy (Matrix.toEuclideanLin A) (WithLp.toLp 2 (star x)) := by
  unfold quadratic RowColumn.energy
  apply congrArg Complex.re
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, RCLike.inner_apply,
    Pi.star_apply, starRingEnd_apply, star_star, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma posSemidef_of_quadratic (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (h : ∀ x, 0 ≤ quadratic A x) : A.PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr hA, fun x => ?_⟩
  have hh := h (star (WithLp.ofLp x))
  rw [quadratic_eq_energy] at hh
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x ((Matrix.toEuclideanLin A) x)).re
  simpa only [star_star, WithLp.toLp_ofLp, RowColumn.energy] using hh

omit [DecidableEq I] in
lemma quadratic_smul (t : ℝ) (A : Matrix I I ℂ) (x : I → ℂ) :
    quadratic (t • A) x = t * quadratic A x := by
  unfold quadratic
  simp only [Matrix.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

omit [DecidableEq I] in
lemma quadratic_sub (A B : Matrix I I ℂ) (x : I → ℂ) :
    quadratic (A-B) x = quadratic A x-quadratic B x := by
  simp [quadratic, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq I] in
lemma quadratic_sum {D : Type*} [Fintype D] (A : D → Matrix I I ℂ) (x : I → ℂ) :
    quadratic (∑ d, A d) x = ∑ d, quadratic (A d) x := by
  simp only [quadratic, Matrix.sum_apply, Finset.sum_mul, Complex.re_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  exact Finset.sum_comm

lemma le_of_quadratic_le (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, quadratic A x ≤ quadratic B x) : A ≤ B := by
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef]
  exact posSemidef_of_quadratic (B-A) (hB.sub hA) (fun x => by rw [quadratic_sub]; exact sub_nonneg.mpr (h x))

lemma quadratic_pinch {B : Type*} [Fintype B] [DecidableEq B]
    (b : I → B) (A : Matrix I I ℂ) (x : I → ℂ) :
    quadratic (pinchMatrix b A) x = ∑ z : B, quadratic A (fun i => if b i=z then x i else 0) := by
  simp only [quadratic, pinchMatrix_apply, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (b i)]
  · by_cases h : b i=b j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

end RowColumn.MatrixState

namespace RowColumn.Signed
open RowColumn.MatrixState CubeShuffle.Specht
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_apply (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (w v : Words (S := S) odd k) :
    intertwinerMatrix line T w v=T (wordVector v) w := by
  rw [← matrix_wordVector odd k (intertwinerMatrix line T) w v]
  simp only [intertwinerMatrix, StarAlgEquiv.apply_symm_apply]
  rfl

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_positive (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    (intertwinerMatrix line T).PosSemidef := by
  rw [← toEuclideanCLM_positive_iff]
  rw [intertwinerMatrix, StarAlgEquiv.apply_symm_apply,
    ← ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact hT

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma parityPattern_eq_iff (w v : Words (S := S) odd k) :
    parityPattern w=parityPattern v ↔ ∀ i, odd (w.1 i) ↔ odd (v.1 i) := by
  simp [parityPattern, funext_iff]

omit [Fintype L] [DecidableEq L] in
lemma pinch_intertwiner_invariant (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (g : lineGroup line)
    (w v : Words (S := S) odd k) :
    pinchMatrix parityPattern (intertwinerMatrix line T) (actWord g.1 w) (actWord g.1 v) =
      pinchMatrix parityPattern (intertwinerMatrix line T) w v := by
  have hp : parityPattern (actWord g.1 w)=parityPattern (actWord g.1 v) ↔ parityPattern w=parityPattern v := by
    simp only [parityPattern_eq_iff, actWord_apply]
    constructor
    · intro h i; simpa using h (g.1 i)
    · intro h i; exact h _
  simp only [pinchMatrix_apply, hp]
  by_cases h : parityPattern w=parityPattern v
  · simp only [h, ite_true, intertwinerMatrix_apply]
    have hr := commuting_coefficient_relation line T g w v
    rw [oddPerm_parity_congr g.1 w v (parityPattern_eq_iff w v |>.mp h)] at hr
    have hs := congrArg (fun z => permSign (oddPerm g.1 v)*z) hr
    simpa only [← mul_assoc, permSign_sq, one_mul] using hs
  · simp only [h, ite_false]

omit [DecidableEq L] in
lemma intertwiner_le_pinch (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    intertwinerMatrix line T ≤
      (((Fintype.card S+1)^(Fintype.card L*Fintype.card C^2) : ℕ) : ℝ) •
        pinchMatrix parityPattern (intertwinerMatrix line T) := by
  have hM := intertwinerMatrix_positive line T hT
  apply le_of_quadratic_le _ _ hM.isHermitian
    ((pinchMatrix_positive parityPattern _ hM).smul (by positivity : (0 : ℝ) ≤ _)).isHermitian
  intro x
  rw [quadratic_smul, quadratic_pinch]
  simp only [quadratic_eq_energy]
  have he : Matrix.toEuclideanLin (intertwinerMatrix line T)=T.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap ((Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply T.toLinearMap.toContinuousLinearMap)
  rw [he]
  convert line_signed_parity_dephasing line T hT (WithLp.toLp 2 (star x)) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ext w
  simp only [parityMask, WithLp.ofLp_toLp, Pi.star_apply]
  split_ifs <;> simp

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] in
lemma extendMatrix_equiv (e : J ↪ I) (p : Equiv.Perm I) (q : Equiv.Perm J)
    (he : ∀ j, p (e j)=e (q j)) (A : Matrix J J ℂ)
    (hA : ∀ i j, A (q i) (q j)=A i j) (i j : I) :
    extendMatrix e A (p i) (p j)=extendMatrix e A i j := by
  have hh (x : I) (hx : x ∉ Set.range e) : p x ∉ Set.range e := by
    rintro ⟨k,hk⟩
    apply hx
    refine ⟨q.symm k, p.injective ?_⟩
    rw [he, Equiv.apply_symm_apply, hk]
  by_cases hi : i ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hj
      rw [he, he, extendMatrix_apply, extendMatrix_apply, hA]
    · rw [extendMatrix_eq_zero_right e A _ _ (hh j hj), extendMatrix_eq_zero_right e A _ _ hj]
  · rw [extendMatrix_eq_zero_left e A _ (hh i hi), extendMatrix_eq_zero_left e A _ hi]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma submatrix_mono (A B : Matrix I I ℂ) (h : A ≤ B) (e : J → I) :
    A.submatrix e e ≤ B.submatrix e e := by
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef] at h ⊢
  exact h.submatrix e

end RowColumn.MatrixState

namespace RowColumn.Signed
open RowColumn.MatrixState RowColumn.Postselection RowColumn.WordOrbits
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] (odd : C → Prop) [DecidablePred odd] (k : ℕ)

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_positive (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    (extendedPinch odd k line T).PosSemidef :=
  extendMatrix_positive _ _ (pinchMatrix_positive _ _ (intertwinerMatrix_positive line T hT))

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_trace (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) :
    (extendedPinch odd k line T).trace = (intertwinerMatrix line T).trace := by
  rw [extendedPinch, extendMatrix_trace, pinchMatrix_trace]

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_invariant (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (p : Equiv.Perm S)
    (hp : ∀ i, line (p i)=line i) (w v : S → C) :
    extendedPinch odd k line T (w ∘ p) (v ∘ p)=extendedPinch odd k line T w v := by
  let g : lineGroup line := ⟨p⁻¹, (lineGroup line).inv_mem hp⟩
  apply extendMatrix_equiv (wordInclusion odd k) (reindexWord p) (wordsEquiv g.1)
  · intro j
    ext i
    change j.1 (p i) = j.1 ((p⁻¹)⁻¹ i)
    rw [inv_inv]
  · exact pinch_intertwiner_invariant line T g

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_support (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (w v : S → C)
    (h : ¬ ∀ i, odd (w i) ↔ odd (v i)) : extendedPinch odd k line T w v=0 := by
  by_cases hw : w ∈ Set.range (wordInclusion (S := S) odd k)
  · obtain ⟨w,rfl⟩ := hw
    by_cases hv : v ∈ Set.range (wordInclusion (S := S) odd k)
    · obtain ⟨v,rfl⟩ := hv
      rw [extendedPinch, extendMatrix_apply]
      apply pinchMatrix_support
      exact fun he => h ((parityPattern_eq_iff w v).mp he)
    · exact extendMatrix_eq_zero_right _ _ _ _ hv
  · exact extendMatrix_eq_zero_left _ _ _ hw _

/-- Finite positive even product-state majorant of the true signed line
commutant. Both parity bandwidth and the local-state normalization are retained. -/
theorem signed_line_postselection (line : S → L) (a₀ : S → C × C)
    (hn : 0 < Fintype.card S)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    intertwinerMatrix line T ≤
      ((((Fintype.card S+1)^(Fintype.card L*Fintype.card C^2) : ℕ) : ℝ) *
        (intertwinerMatrix line T).trace.re *
        (((Fintype.card S+1)^(Fintype.card (L × (C × C))) : ℕ) /
          (Fintype.card (Phases (L × (C × C)) (Fintype.card S)) : ℝ))) •
      (∑ q : Types (S := S) (A := L × (C × C)),
        ∑ θ : Phases (L × (C × C)) (Fintype.card S),
          sectorTensor odd k (fun i => lineState line a₀ odd q θ (line i))) := by
  let A := extendedPinch odd k line T
  let B := ∑ q : Types (S := S) (A := L × (C × C)),
    ∑ θ : Phases (L × (C × C)) (Fintype.card S),
      tensorMatrix (fun i : S => lineState line a₀ odd q θ (line i))
  let t : ℝ := (intertwinerMatrix line T).trace.re *
    (((Fintype.card S+1)^(Fintype.card (L × (C × C))) : ℕ) /
      (Fintype.card (Phases (L × (C × C)) (Fintype.card S)) : ℝ))
  have hA : A.PosSemidef := extendedPinch_positive odd k line T hT
  have ht : 0 ≤ t := mul_nonneg (by
    have hh := (intertwinerMatrix_positive line T hT).trace_nonneg
    exact hh.1) (by positivity)
  have hB : B.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro q _
    apply Finset.sum_nonneg
    intro θ _
    exact (tensorMatrix_posSemidef _ (fun i => lineState_positive line a₀ odd q θ (line i))).nonneg
  have hab : A ≤ t • B := by
    apply le_of_quadratic_le _ _ hA.isHermitian (hB.smul ht).isHermitian
    intro x
    simp only [quadratic_smul, B, quadratic_sum]
    have hh := positive_line_postselection line a₀ hn odd A hA
      (extendedPinch_invariant odd k line T) (extendedPinch_support odd k line T) x
    simpa only [A, extendedPinch_trace, t, mul_assoc] using hh
  have hsub := submatrix_mono A (t • B) hab (Subtype.val : Words (S := S) odd k → S → C)
  have hleft : A.submatrix Subtype.val Subtype.val=pinchMatrix parityPattern (intertwinerMatrix line T) := by
    ext w v
    exact extendMatrix_apply (wordInclusion odd k) _ w v
  rw [hleft] at hsub
  have hs := smul_le_smul_of_nonneg_left hsub
    (by positivity : (0 : ℝ) ≤ (((Fintype.card S+1)^(Fintype.card L*Fintype.card C^2) : ℕ) : ℝ))
  apply (intertwiner_le_pinch line T hT).trans
  convert hs using 1
  ext w v
  simp only [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.sum_apply, B, t,
    sectorTensor, smul_smul, mul_assoc]

end RowColumn.Signed

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_OverlapBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.Signed
open MatrixState Postselection WordOrbits
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L]

omit [DecidableEq S] in
lemma phases_card : Fintype.card (Phases (L × (C × C)) (Fintype.card S)) = lineCost (S := S) (C := C) (L := L) := by
  simp only [Phases, Fintype.card_fun, ZMod.card, Fintype.card_prod, lineCost, pow_two]
omit [DecidableEq S] in
lemma types_card : Fintype.card (Types (S := S) (A := L × (C × C))) = lineCost (S := S) (C := C) (L := L) := by
  simp only [Types, CountIndex, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, lineCost, pow_two]
omit [DecidableEq S] in
lemma mixtureIndex_card : Fintype.card (MixtureIndex (S := S) (C := C) (L := L)) = lineCost (S := S) (C := C) (L := L)^2 := by
  simp only [MixtureIndex, Fintype.card_prod, types_card, phases_card, pow_two]
omit [DecidableEq S] [DecidableEq C] [DecidableEq L] in
lemma lineCost_pos : 0 < lineCost (S := S) (C := C) (L := L) := pow_pos (Nat.succ_pos _) _

variable (odd : C → Prop) [DecidablePred odd] (k : ℕ)

theorem signed_line_mixture (line : S → L) (a₀ : S → C × C) (hn : 0 < Fintype.card S)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    intertwinerMatrix line T ≤
      ((lineCost (S := S) (C := C) (L := L) : ℝ) * (intertwinerMatrix line T).trace.re) •
        ∑ z : MixtureIndex (S := S) (C := C) (L := L),
          sectorTensor odd k (fun i => lineState line a₀ odd z.1 z.2 (line i)) := by
  have hz : (lineCost (S := S) (C := C) (L := L) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lineCost_pos (S := S) (C := C) (L := L)))
  have hh := signed_line_postselection odd k line a₀ hn T hT
  simp only [lineCost] at hz ⊢
  simpa only [Fintype.card_prod, ← pow_two, phases_card, lineCost, div_self hz, mul_one,
    Fintype.sum_prod_type] using hh

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I U V : Type*} [Fintype I] [DecidableEq I] [Fintype U] [Fintype V]

lemma filtered_trace_mono (A B A' B' Q : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hA' : A'.PosSemidef)
    (hQ : Q.IsHermitian) (hQA : Q*A=A) (hQB : Q*B=B)
    (hAA : A ≤ A') (hBB : B ≤ B') :
    (A*B).trace.re ≤ (A'*Q*B'*Q).trace.re := by
  have hAQ : A*Q=A := by
    have hh := congrArg Matrix.conjTranspose hQA
    simpa only [Matrix.conjTranspose_mul,hA.isHermitian.eq,hQ.eq] using hh
  have hBQ : B*Q=B := by
    have hh := congrArg Matrix.conjTranspose hQB
    simpa only [Matrix.conjTranspose_mul,hB.isHermitian.eq,hQ.eq] using hh
  have hp : (Q*A'*Q).PosSemidef := by
    simpa only [hQ.eq] using hA'.conjTranspose_mul_mul_same Q
  calc
    _ ≤ (A'*B).trace.re := trace_mul_mono A A' B hAA hB
    _ = (B*(Q*A'*Q)).trace.re := by
      symm
      simp only [← mul_assoc]
      rw [hBQ, Matrix.trace_mul_cycle, hQB, Matrix.trace_mul_comm]
    _ ≤ (B'*(Q*A'*Q)).trace.re := trace_mul_mono B B' _ hBB hp
    _ = _ := by
      calc
        _ = ((B'*Q)*(A'*Q)).trace.re := by simp only [mul_assoc]
        _ = ((A'*Q)*(B'*Q)).trace.re := congrArg Complex.re (Matrix.trace_mul_comm _ _)
        _ = _ := by simp only [mul_assoc]

lemma trace_filtered_smul_sum (a b : ℝ) (S : U → Matrix I I ℂ) (T : V → Matrix I I ℂ)
    (Q : Matrix I I ℂ) :
    ((a • ∑ i, S i)*Q*(b • ∑ j, T j)*Q).trace.re =
      a*b*∑ i, ∑ j, (S i*Q*T j*Q).trace.re := by
  simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum, Complex.re_sum, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_mixture_bound (A B Q : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hQ : Q.IsHermitian)
    (hQA : Q*A=A) (hQB : Q*B=B)
    (S : U → Matrix I I ℂ) (T : V → Matrix I I ℂ)
    (hS : ∀ i, (S i).PosSemidef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAS : A ≤ a • ∑ i, S i) (hBT : B ≤ b • ∑ j, T j)
    (z : ℝ) (hz : ∀ i j, (S i*Q*T j*Q).trace.re ≤ z) :
    (A*B).trace.re ≤ a*b * ((Fintype.card U : ℝ)*Fintype.card V) * z := by
  have hS' : (∑ i, S i).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ => (hS i).nonneg)
  apply (filtered_trace_mono A B _ _ Q hA hB (hS'.smul ha)
    hQ hQA hQB hAS hBT).trans
  rw [trace_filtered_smul_sum]
  have hh := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hz i j
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg ha hb)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh'

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open Signed Postselection WordOrbits FiniteStarAlgebra
variable {S C L K : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] [Nonempty S]

/-- Reconstruction of the occupied overlap for the actual signed row/column
commutants. The two trace factors retain every prescribed copy. -/
theorem occupied_commutant_trace_oai (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (e : S ↪ L × K) (a₀ : S → C × C)
    (A : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) (fun i => (e i).1))
      (lineRepresentation (odd := odd) (k := k) (fun i => (e i).1)))
    (B : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) (fun i => (e i).2))
      (lineRepresentation (odd := odd) (k := k) (fun i => (e i).2)))
    (hA : A.toLinearMap.IsPositive) (hB : B.toLinearMap.IsPositive)
    (q : sectorAlgebra (S := S) odd k) (hqs : star q=q) (hqq : q*q=q) (hqc : ∀ a, q*a=a*q)
    (d : ℝ) (hd : 0<d)
    (hfilter : ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
      ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / d)
    (hQA : algebraMatrix (sectorAlgebra (S := S) odd k) q * intertwinerMatrix (fun i => (e i).1) A =
      intertwinerMatrix (fun i => (e i).1) A)
    (hQB : algebraMatrix (sectorAlgebra (S := S) odd k) q * intertwinerMatrix (fun i => (e i).2) B =
      intertwinerMatrix (fun i => (e i).2) B) :
    (intertwinerMatrix (fun i => (e i).1) A * intertwinerMatrix (fun i => (e i).2) B).trace.re ≤
      16 * (lineCost (S := S) (C := C) (L := L) : ℝ)^3 *
        (lineCost (S := S) (C := C) (L := K) : ℝ)^3 *
        (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2 *
        Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ) *
        (intertwinerMatrix (fun i => (e i).1) A).trace.re *
        (intertwinerMatrix (fun i => (e i).2) B).trace.re / d := by
  let l := fun i => (e i).1
  let r := fun i => (e i).2
  let M := fun z : MixtureIndex (S := S) (C := C) (L := L) => lineState l a₀ odd z.1 z.2
  let N := fun z : MixtureIndex (S := S) (C := C) (L := K) => lineState r a₀ odd z.1 z.2
  have hM z i : (M z i).PosSemidef := lineState_positive l a₀ odd z.1 z.2 i
  have hN z i : (N z i).PosSemidef := lineState_positive r a₀ odd z.1 z.2 i
  have heM z i : M z i ∈ evenAlgebra odd := lineState_even l a₀ odd z.1 z.2 i
  have heN z i : N z i ∈ evenAlgebra odd := lineState_even r a₀ odd z.1 z.2 i
  have htM z i : (M z i).trace.re ≤ 1 := lineState_trace l a₀ odd z.1 z.2 i
  have htN z i : (N z i).trace.re ≤ 1 := lineState_trace r a₀ odd z.1 z.2 i
  have hAp := intertwinerMatrix_positive l A hA
  have hBp := intertwinerMatrix_positive r B hB
  have hAS := signed_line_mixture odd k l a₀ Fintype.card_pos A hA
  have hBN := signed_line_mixture odd k r a₀ Fintype.card_pos B hB
  have hz z w := sector_filtered_trace_bound odd k e q hqs hqq hqc d hd hfilter
    (M z) (N w) (hM z) (hN w) (heM z) (heN w) (htM z) (htN w)
  have hh := trace_mixture_bound (intertwinerMatrix l A) (intertwinerMatrix r B)
    (algebraMatrix (sectorAlgebra (S := S) odd k) q) hAp hBp (algebraMatrix_hermitian _ q hqs)
    hQA hQB (fun z => sectorTensor odd k (fun i => M z (l i)))
    (fun w => sectorTensor odd k (fun i => N w (r i)))
    (fun z => sectorTensor_positive odd k _ (fun i => hM z (l i)))
    ((lineCost (S := S) (C := C) (L := L) : ℝ) * (intertwinerMatrix l A).trace.re)
    ((lineCost (S := S) (C := C) (L := K) : ℝ) * (intertwinerMatrix r B).trace.re)
    (mul_nonneg (Nat.cast_nonneg _) hAp.trace_nonneg.1)
    (mul_nonneg (Nat.cast_nonneg _) hBp.trace_nonneg.1) hAS hBN _ hz
  apply hh.trans_eq
  simp only [mixtureIndex_card, Nat.cast_pow]
  ring

end RowColumn.MatrixState

end
end


end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.RowColumn.MatrixState.occupied_commutant_trace_oai.{u_1, u_2, u_3, u_4} := @OAI.RowColumn.MatrixState.occupied_commutant_trace_oai.{u_1, u_2, u_3, u_4}
