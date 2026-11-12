-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:31.521954+00:00
-- url     : https://prove2.me/submissions/ce65e4ed-396d-4dba-a66b-dac160e6f4d0

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P006

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_SubspaceCountingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.BucketSampler.directionZero_isEmpty _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace UniqueGamesTheorem.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem span_generators (S : Submodule K V) (k : ℕ) (h : finrank K S = k) :
    Submodule.span K (Set.range (generators S k h)) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  change Submodule.span K (Set.range (S.subtype ∘ b)) = S
  rw [Set.range_comp, Submodule.span_image, b.span_eq]
  simp

/-- A k-subspace is determined by a chosen ordered k-tuple of spanning vectors. -/
theorem card_subspaces_rank_le [Finite V] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤ Nat.card V ^ k := by
  classical
  let code : {S : Submodule K V // finrank K S = k} → (Fin k → V) :=
    fun S => generators S.1 k S.2
  have hinj : Function.Injective code := by
    intro S T h
    apply Subtype.ext
    calc
      S.1 = Submodule.span K (Set.range (code S)) := (span_generators S.1 k S.2).symm
      _ = Submodule.span K (Set.range (code T)) :=
        congrArg (fun f : Fin k → V => Submodule.span K (Set.range f)) h
      _ = T.1 := span_generators T.1 k T.2
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hinj

/-- General finite-field form of the image-choice estimate in A.4. -/
theorem card_subspaces_rank_le_field_power [Finite K] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤
      Nat.card K ^ (finrank K V * k) := by
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  have h := card_subspaces_rank_le (K := K) (V := V) k
  rwa [Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_mul] at h

/-- Binary specialization: the ambient dimension is the dimension of Y's image,
not the potentially much larger original vector space. -/
theorem card_binary_subspaces_rank_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (d k : ℕ) (hd : finrank (ZMod 2) V ≤ d) :
    Nat.card {S : Submodule (ZMod 2) V // finrank (ZMod 2) S = k} ≤
      2 ^ (d * k) := by
  calc
    _ ≤ Nat.card (ZMod 2) ^ (finrank (ZMod 2) V * k) :=
      card_subspaces_rank_le_field_power (K := ZMod 2) (V := V) k
    _ = 2 ^ (finrank (ZMod 2) V * k) := by simp
    _ ≤ 2 ^ (d * k) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k hd)

end UniqueGamesTheorem.Appendix.SubspaceCounting

end

section

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace UniqueGamesTheorem.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_horizontal [FiniteDimensional K V] (B : Submodule K V) :
    Module.finrank K (horizontal B) = Module.finrank K B := (horizontalEquiv B).finrank_eq.symm

theorem finrank_extension [FiniteDimensional K V] (B : Submodule K V) (q : V ⧸ B) :
    Module.finrank K (extension B q) = Module.finrank K B + 1 := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have h := (extensionEquiv B q v hv).finrank_eq.symm
  simpa only [Module.finrank_prod,Module.finrank_self] using h

theorem card_eq_pow_finrank [Finite K] [Finite V] [FiniteDimensional K V] :
    Nat.card V = Nat.card K ^ Module.finrank K V := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite V
  have h := Fintype.card_congr (Module.finBasis K V).equivFun.toEquiv
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.card_eq_fintype_card] using h

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.SubspaceExtensions.subspaceFintype
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.SubspaceExtensions.quotientFintype
theorem quotient_card_mul_pow [Finite K] [Finite V] [FiniteDimensional K V] (B : Submodule K V) :
    (Nat.card (V ⧸ B) : ℤ) * (Nat.card K : ℤ)^Module.finrank K B =
      (Nat.card K : ℤ)^Module.finrank K V := by
  rw [card_eq_pow_finrank (K:=K) (V:=V ⧸ B)]
  simp only [Nat.cast_pow]
  rw [← pow_add, B.finrank_quotient_add_finrank]

theorem weightedTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V × K) w =
      ∑ B : Submodule K V, (w (Module.finrank K B) +
        (Nat.card (V ⧸ B) : ℤ) * w (Module.finrank K B + 1)) := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ a : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B),
        w (Module.finrank K (encode a)) :=
      (Equiv.sum_comp ((splitEquiv (K:=K) (V:=V)).symm) _).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type,Fintype.sum_sigma,encode,Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro B _
        exact congrArg w (finrank_horizontal B)
      · apply Finset.sum_congr rfl
        intro B _
        calc
          _ = ∑ _q : V ⧸ B, w (Module.finrank K B + 1) := by
            apply Finset.sum_congr rfl
            intro q _
            exact congrArg w (finrank_extension B q)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem mobiusTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V × K) =
      (1 - (Nat.card K : ℤ)^Module.finrank K V) * mobiusTotal (K:=K) (V:=V) := by
  classical
  unfold mobiusTotal
  rw [weightedTotal_prod]
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, (1-(Nat.card K:ℤ)^Module.finrank K V) *
        mobiusWeight (Nat.card K) (Module.finrank K B) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [mobiusWeight]
      have hcard := quotient_card_mul_pow (K:=K) B
      calc
        _ = mobiusWeight (Nat.card K) (Module.finrank K B) -
            ((Nat.card (V ⧸ B):ℤ)*(Nat.card K:ℤ)^Module.finrank K B) *
              mobiusWeight (Nat.card K) (Module.finrank K B) := by ring
        _ = _ := by rw [hcard]; ring
    _ = _ := by rw [Finset.mul_sum]

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem finrank_map_equiv (e : V ≃ₗ[K] W) (B : Submodule K V) :
    Module.finrank K (B.map e.toLinearMap) = Module.finrank K B := (subspaceMapEquiv e B).finrank_eq.symm

theorem weightedTotal_equiv [Finite V] [Finite W] (e : V ≃ₗ[K] W) (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V) w = weightedTotal (K:=K) (V:=W) w := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, w (Module.finrank K (B.map e.toLinearMap)) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [finrank_map_equiv]
    _ = _ := by
      change (∑ B : Submodule K V, w (Module.finrank K (subspaceEquiv e B))) = _
      exact Equiv.sum_comp (subspaceEquiv e) (fun B : Submodule K W => w (Module.finrank K B))

theorem mobiusTotal_equiv [Finite K] [Finite V] [Finite W] (e : V ≃ₗ[K] W) :
    mobiusTotal (K:=K) (V:=V) = mobiusTotal (K:=K) (V:=W) :=
  weightedTotal_equiv e _

theorem mobiusTotal_subsingleton [Finite K] [Finite V] [Subsingleton V] :
    mobiusTotal (K:=K) (V:=V) = 1 := by
  classical
  have hB : ∀ B : Submodule K V, B = ⊥ := by
    intro B
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  unfold mobiusTotal weightedTotal
  rw [Finset.sum_eq_single ⊥]
  · simp [mobiusWeight]
  · intro B _ hne
    exact (hne (hB B)).elim
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem coordinate_total_succ [Finite K] (n : Nat) :
    mobiusTotal (K:=K) (V:=Fin (n+1) → K) = 0 := by
  induction n with
  | zero =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) 0),mobiusTotal_prod]
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) (n+1)),mobiusTotal_prod,ih,mul_zero]

theorem mobiusTotal_eq_if [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V) = if Module.finrank K V = 0 then 1 else 0 := by
  rw [mobiusTotal_equiv (Module.finBasis K V).equivFun]
  cases hd : Module.finrank K V with
  | zero => simpa [hd] using (mobiusTotal_subsingleton (K:=K) (V:=Fin 0 → K))
  | succ n => simpa [hd] using (coordinate_total_succ (K:=K) n)

theorem mobiusWeight_closed (q n : Nat) :
    mobiusWeight q n = (-1:ℤ)^n * (q:ℤ)^(n.choose 2) := by
  induction n with
  | zero => simp [mobiusWeight]
  | succ n ih =>
    rw [mobiusWeight,ih,Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,pow_add,pow_succ]
    ring

theorem binary_subspace_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] :
    weightedTotal (K:=ZMod 2) (V:=E) (fun d => (-1:ℤ)^d * 2^(d.choose 2)) =
      if Module.finrank (ZMod 2) E = 0 then 1 else 0 := by
  have h := mobiusTotal_eq_if (K:=ZMod 2) (V:=E)
  have hq : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [mobiusTotal,weightedTotal,mobiusWeight_closed,hq,Nat.cast_ofNat] using h

end
end UniqueGamesTheorem.Appendix.SubspaceExtensions

end

section

namespace UniqueGamesTheorem.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

theorem lowerInterval_finrank (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    finrank 𝕜 (lowerIntervalEquiv I A) = finrank 𝕜 A.val :=
  (lowerIntervalSpaceEquiv I A).finrank_eq.symm

open scoped BigOperators
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.SubmoduleInterval.submoduleFinite
theorem lowerWeightedTotal_eq [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) :
    lowerWeightedTotal I w = SubspaceExtensions.weightedTotal (K := 𝕜) (V := I) w := by
  classical
  let := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  let := SubspaceExtensions.subspaceFintype (K := 𝕜) (V := I)
  unfold lowerWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (lowerIntervalEquiv I)
    (fun A : {A : Submodule 𝕜 V // A ≤ I} => w (finrank 𝕜 A.val))
    (fun B : Submodule 𝕜 I => w (finrank 𝕜 B))
    (fun A => congrArg w (lowerInterval_finrank I A).symm)

theorem binary_lower_interval_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] (I : Submodule (ZMod 2) E) :
    lowerWeightedTotal I (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if I = ⊥ then 1 else 0 := by
  rw [lowerWeightedTotal_eq, SubspaceExtensions.binary_subspace_mobius]
  simp only [Submodule.finrank_eq_zero]

end UniqueGamesTheorem.Appendix.SubmoduleInterval

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_AntecedentCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.UpperMobius
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
attribute [local instance] Classical.propDecidable
variable {W : Type*} [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 W] [Finite W]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.UpperMobius.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.UpperMobius.dualFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.UpperMobius.submoduleFinite
omit [FiniteDimensional F2 W] [Finite W] in
theorem quotient_comap_codim (K : Submodule F2 W)
    (S : Submodule F2 (W ⧸ K)) :
    Module.finrank F2 (W ⧸ S.comap K.mkQ) =
      Module.finrank F2 ((W ⧸ K) ⧸ S) := by
  let π := S.mkQ.comp K.mkQ
  have hπ : Function.Surjective π := S.mkQ_surjective.comp K.mkQ_surjective
  have hker : π.ker = S.comap K.mkQ := by simp [π, LinearMap.ker_comp]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq.symm.trans
    (π.quotKerEquivOfSurjective hπ).finrank_eq

omit [FiniteDimensional F2 W] [Finite W] in
theorem upperQuotientEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) := by
  have hB : (upperQuotientEquiv K B).comap K.mkQ = B.val :=
    congrArg Subtype.val ((Submodule.comapMkQRelIso K).apply_symm_apply B)
  exact (Submodule.quotEquivOfEq _ _ hB).finrank_eq.symm.trans
    (quotient_comap_codim K (upperQuotientEquiv K B))

omit [Finite W] in
theorem upperDualSubspaceEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 (upperDualSubspaceEquiv K B) := by
  calc
    _ = Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) :=
      upperQuotientEquiv_codim K B
    _ = Module.finrank F2 (upperQuotientEquiv K B).dualAnnihilator :=
      (Subspace.quotEquivAnnihilator (upperQuotientEquiv K B)).finrank_eq
    _ = _ := rfl

theorem upperWeightedTotal_eq_dual (K : Submodule F2 W) (w : ℕ → ℤ) :
    upperWeightedTotal K w =
      SubspaceExtensions.weightedTotal
        (K := F2) (V := Module.Dual F2 (W ⧸ K)) w := by
  classical
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  let := SubspaceExtensions.subspaceFintype (K := F2) (V := Module.Dual F2 (W ⧸ K))
  unfold upperWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (upperDualSubspaceEquiv K)
    (fun B : {B : Submodule F2 W // K ≤ B} => w (Module.finrank F2 (W ⧸ B.val)))
    (fun S : Submodule F2 (Module.Dual F2 (W ⧸ K)) => w (Module.finrank F2 S))
    (fun B => congrArg w (upperDualSubspaceEquiv_codim K B))

omit [Finite W] in
theorem quotient_finrank_zero_iff (K : Submodule F2 W) :
    Module.finrank F2 (W ⧸ K) = 0 ↔ K = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := K.finrank_quotient_add_finrank
    omega
  · intro h
    subst K
    have hr := (⊤ : Submodule F2 W).finrank_quotient_add_finrank
    rw [finrank_top] at hr
    omega

theorem binary_upper_interval_mobius (K : Submodule F2 W) :
    upperWeightedTotal K (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if K = ⊤ then 1 else 0 := by
  classical
  rw [upperWeightedTotal_eq_dual]
  rw [SubspaceExtensions.binary_subspace_mobius]
  simp only [Subspace.dual_finrank_eq, quotient_finrank_zero_iff]
end UniqueGamesTheorem.Appendix.UpperMobius

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_DyadicError
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.DyadicError

private theorem pow_le_one_aux (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    q^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih hq0).trans (by simpa using hq1)

private theorem pow_antitone_aux (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (a b : ℕ) (hab : a ≤ b) : q^b ≤ q^a := by
  have hb : a + (b-a) = b :=
    (Nat.add_comm a (b-a)).trans (Nat.sub_add_cancel hab)
  calc
    q^b = q^(a+(b-a)) := congrArg (fun n : ℕ => q^n) hb.symm
    _ = q^a * q^(b-a) := by rw [pow_add]
    _ ≤ q^a * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one_aux q hq0 hq1 (b-a)) (pow_nonneg hq0 a)
    _ = q^a := mul_one _

theorem half_power_le_quarter (d n : ℕ) (hd : 1 ≤ d) :
    (1/2 : ℝ)^(3*d*n) ≤ (1/4 : ℝ)^n := by
  have h3 : 2 ≤ 3*d := le_trans (by decide : 2 ≤ 3)
    (by simpa using Nat.mul_le_mul_left 3 hd)
  have hexp : 2*n ≤ 3*d*n := Nat.mul_le_mul_right n h3
  calc
    (1/2 : ℝ)^(3*d*n) ≤ (1/2 : ℝ)^(2*n) :=
      pow_antitone_aux (1/2) (by norm_num) (by norm_num) _ _ hexp
    _ = (1/4 : ℝ)^n := by
      rw [pow_mul]
      congr 1
      norm_num

theorem quarterSum_nonneg (n : ℕ) : 0 ≤ quarterSum n := by
  unfold quarterSum
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (by norm_num : (0:ℝ)≤1/4) i)

theorem quarterSum_residual (n : ℕ) :
    quarterSum n + (4/3 : ℝ)*(1/4 : ℝ)^n = 4/3 := by
  induction n with
  | zero => norm_num [quarterSum]
  | succ n ih =>
    have hstep : quarterSum (n+1) = quarterSum n + (1/4 : ℝ)^n := by
      exact Finset.sum_range_succ _ _
    rw [hstep, pow_succ]
    nlinarith

theorem quarterSum_le (n : ℕ) : quarterSum n ≤ (4/3 : ℝ) := by
  have hp : (0 : ℝ) ≤ (1/4 : ℝ)^n := pow_nonneg (by norm_num) n
  have h := quarterSum_residual n
  nlinarith

theorem quarterError_add_one (n : ℕ) (hn : 0 < n) :
    quarterError n + 1 = (quarterSum n)^2 := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hpair (i j : ℕ) :
      (if i=0 ∧ j=0 then (0:ℝ) else (1/4 : ℝ)^(i+j)) +
        (if i=0 ∧ j=0 then (1:ℝ) else 0) =
          (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [hi,hj,pow_add]
  have hsum : quarterError n +
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i=0 ∧ j=0 then (1:ℝ) else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    unfold quarterError
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hpair i j
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range n, if i=0 ∧ j=0 then (1:ℝ) else 0) =
        if i=0 then 1 else 0 := by
    by_cases hi : i=0
    · simp [hi,h0]
    · simp [hi]
  have hdelta : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i=0 ∧ j=0 then (1:ℝ) else 0) = 1 := by
    simp_rw [hinner]
    simp [h0]
  have hproduct : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (1/4 : ℝ)^i * (1/4 : ℝ)^j) = (quarterSum n)^2 := by
    simp only [quarterSum,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hdelta,hproduct] at hsum
  exact hsum

theorem quarterError_le_seven_ninths (n : ℕ) (hn : 0 < n) :
    quarterError n ≤ (7/9 : ℝ) := by
  have hbound := quarterSum_le n
  have hnonneg := quarterSum_nonneg n
  have hsq := mul_le_mul hbound hbound hnonneg (by norm_num : (0:ℝ)≤4/3)
  have hid := quarterError_add_one n hn
  nlinarith

theorem dyadicError_le_quarterError (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ quarterError (d+1) := by
  unfold dyadicError quarterError
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hzero : i=0 ∧ j=0
  · simp [hzero]
  · simp only [hzero]
    exact half_power_le_quarter d (i+j) hd

theorem dyadicError_le_seven_ninths (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ (7/9 : ℝ) :=
  (dyadicError_le_quarterError d hd).trans
    (quarterError_le_seven_ninths (d+1) (Nat.succ_pos d))

theorem finite_dyadic_error_le_one (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
      if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))) ≤ 1 := by
  change dyadicError d ≤ 1
  exact (dyadicError_le_seven_ninths d hd).trans (by norm_num)

end UniqueGamesTheorem.Appendix.DyadicError

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_BadConvolution
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The signed bad-convolution term of Appendix A.1.  The selector here is
the weak image/kernel selector, prior to its separate A.4 decomposition. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.BadConvolution
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

private theorem sum_masked_eq_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] (f : α → M) :
    (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro a; simp) f

variable [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

omit [Finite W] [Finite V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem pairDimension_eq_zero_iff (p : Submodule F2 V × Submodule F2 W) :
    pairDimension p = 0 ↔ p = (⊥,⊤) := by
  rw [pairDimension, Nat.add_eq_zero_iff]
  rw [Submodule.finrank_eq_zero, UpperMobius.quotient_finrank_zero_iff]
  constructor
  · rintro ⟨hA,hB⟩
    exact Prod.ext hA hB
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem lower_mobius_sum (I : Submodule F2 V) :
    (∑ A : Submodule F2 V, if A ≤ I then mobius (finrank F2 A) else 0) =
      if I = ⊥ then 1 else 0 := by
  let := Fintype.ofFinite {A : Submodule F2 V // A ≤ I}
  rw [sum_masked_eq_subtype]
  have h := SubmoduleInterval.binary_lower_interval_mobius I
  unfold SubmoduleInterval.lowerWeightedTotal at h
  unfold mobius
  exact_mod_cast h

theorem upper_mobius_sum (K : Submodule F2 W) :
    (∑ B : Submodule F2 W, if K ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) =
      if K = ⊤ then 1 else 0 := by
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  rw [sum_masked_eq_subtype]
  have h := UpperMobius.binary_upper_interval_mobius K
  unfold UpperMobius.upperWeightedTotal at h
  unfold mobius
  exact_mod_cast h

omit [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
    [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
private theorem triple_incidence_iff (p : Submodule F2 V × Submodule F2 W)
    (X Y : W →ₗ[F2] V) :
    (Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)) ↔
      p.1 ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range ∧
        (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ p.2 := by
  simp only [Incidence, le_inf_iff, sup_le_iff]
  tauto

theorem triple_mobius_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then pairWeight p else 0) = if Bad X Y then 0 else 1 := by
  simp_rw [triple_incidence_iff]
  calc
    _ = (∑ A : Submodule F2 V,
        if A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range then mobius (finrank F2 A) else 0) *
        (∑ B : Submodule F2 W,
        if (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hA : A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range <;>
        by_cases hB : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B <;>
        simp [pairWeight, hA, hB]
    _ = _ := by
      rw [lower_mobius_sum, upper_mobius_sum]
      by_cases hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥ <;>
        by_cases hk : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker = ⊤ <;>
        simp [Bad, hi, hk]

theorem signed_triple_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then signedWeight p else 0) = if Bad X Y then 1 else 0 := by
  have htop : finrank F2 (W ⧸ (⊤ : Submodule F2 W)) = 0 :=
    (UpperMobius.quotient_finrank_zero_iff ⊤).mpr rfl
  have hterm (p : Submodule F2 V × Submodule F2 W) :
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then pairWeight p else 0) +
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then signedWeight p else 0) = if p = (⊥,⊤) then 1 else 0 := by
    by_cases hp : p = (⊥,⊤)
    · subst p
      simp [Incidence, pairWeight, signedWeight, mobius, htop]
    · by_cases h : Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      all_goals simp [signedWeight, hp, h]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun p _ => hterm p)
  rw [Finset.sum_add_distrib, triple_mobius_sum] at hs
  have hdelta : (∑ p : Submodule F2 V × Submodule F2 W,
      if p = (⊥,⊤) then (1:ℝ) else 0) = 1 := by simp
  rw [hdelta] at hs
  by_cases hbad : Bad X Y <;> simp [hbad] at hs ⊢ <;> linarith

variable [Fintype (W →ₗ[F2] V)]

/-- Exact Möbius expansion; no degree or positivity assumption is used. -/
theorem badConvolution_expansion (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) :
    badConvolution a X =
      ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p * pieceConvolution p.1 p.2 a X else 0 := by
  calc
    _ = ∑ Y, (if Bad X Y then (1:ℝ) else 0) * (a Y * a (X+Y)) := by
      unfold badConvolution
      apply Finset.sum_congr rfl
      intro Y _
      by_cases h : Bad X Y <;> simp [h]
    _ = ∑ Y, ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p *
          (filteredCoefficient p.1 p.2 a Y * filteredCoefficient p.1 p.2 a (X+Y)) else 0 := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← signed_triple_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X <;>
        by_cases hY : Incidence p.1 p.2 Y <;>
        by_cases hZ : Incidence p.1 p.2 (X+Y) <;>
        simp [filteredCoefficient, hX, hY, hZ]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X
      · simp only [hX, ite_true, if_true, pieceConvolution, Finset.mul_sum]
      · simp [hX]

omit [Fintype (Submodule F2 V)] in
theorem card_lower_rank_le (I : Submodule F2 V) (n i : ℕ)
    (hn : finrank F2 I ≤ n) :
    Nat.card {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i} ≤ 2^(n*i) := by
  let : Finite (Submodule F2 I) :=
    Finite.of_injective (fun S : Submodule F2 I => (S : Set I)) SetLike.coe_injective
  let e := SubmoduleInterval.lowerIntervalEquiv I
  let code (A : {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i}) :
      {S : Submodule F2 I // finrank F2 S = i} :=
    ⟨e ⟨A.1, A.2.1⟩,
      (SubmoduleInterval.lowerInterval_finrank I ⟨A.1, A.2.1⟩).trans A.2.2⟩
  have hi : Function.Injective code := by
    intro A B h
    have he : e ⟨A.1, A.2.1⟩ = e ⟨B.1, B.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {A : Submodule F2 V // A ≤ I} => z.val) (e.injective he)
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n i hn)

omit [Finite W] [Fintype (Submodule F2 W)] in
theorem card_upper_codim_le (K : Submodule F2 W) (n j : ℕ)
    (hn : finrank F2 (W ⧸ K) ≤ n) :
    Nat.card {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j} ≤ 2^(n*j) := by
  let D := Module.Dual F2 (W ⧸ K)
  let : Finite D := Finite.of_injective (Module.finBasis F2 D).equivFun
    (Module.finBasis F2 D).equivFun.injective
  let : Finite (Submodule F2 D) :=
    Finite.of_injective (fun S : Submodule F2 D => (S : Set D)) SetLike.coe_injective
  let e := UpperMobius.upperDualSubspaceEquiv K
  let code (B : {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j}) :
      {S : Submodule F2 D // finrank F2 S = j} :=
    ⟨e ⟨B.1, B.2.1⟩,
      (UpperMobius.upperDualSubspaceEquiv_codim K ⟨B.1, B.2.1⟩).symm.trans B.2.2⟩
  have hi : Function.Injective code := by
    intro B C h
    have he : e ⟨B.1, B.2.1⟩ = e ⟨C.1, C.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {B : Submodule F2 W // K ≤ B} => z.val) (e.injective he)
  have hdim : finrank F2 D ≤ n := by
    simpa only [D, Subspace.dual_finrank_eq] using hn
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n j hdim)

private theorem finite_pair_level_sum {α : Type*} (s : Finset α)
    (i j : α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ a ∈ s, i a ≤ d ∧ j a ≤ d)
    (hzero : ∀ a ∈ s, ¬(i a=0 ∧ j a=0))
    (hcount : ∀ u v, (s.filter (fun a => i a=u ∧ j a=v)).card ≤ 2^(2*d*(u+v))) :
    (∑ a ∈ s, (1/2:ℝ)^(5*d*(i a+j a))) ≤ 1 := by
  classical
  have hmap : ∀ a ∈ s, (i a,j a) ∈ Finset.range (d+1) ×ˢ Finset.range (d+1) := by
    intro a ha
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).1),
       Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).2)⟩
  have hcancel (a b : ℕ) :
      (2:ℝ)^a * (1/2:ℝ)^(a+b) = (1/2:ℝ)^b := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    _ = ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(i a+j a)) := by
      have h := Finset.sum_fiberwise_of_maps_to (g := fun a => (i a,j a)) hmap
        (fun a => (1/2:ℝ)^(5*d*(i a+j a)))
      simpa only [Finset.sum_product, Prod.mk.injEq] using h.symm
    _ ≤ ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        if u=0 ∧ v=0 then 0 else (1/2:ℝ)^(3*d*(u+v)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      by_cases hz : u=0 ∧ v=0
      · rw [ite_eq_left hz]
        have hempty : s.filter (fun a => i a=u ∧ j a=v) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro a ha
          have ham := Finset.mem_filter.mp ha
          exact hzero a ham.1 ⟨ham.2.1.trans hz.1, ham.2.2.trans hz.2⟩
        rw [hempty, Finset.sum_empty]
      · rw [ite_eq_right hz]
        have hc : ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) ≤
            (2:ℝ)^(2*d*(u+v)) := by exact_mod_cast hcount u v
        calc
          _ = ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) *
              (1/2:ℝ)^(5*d*(u+v)) := by
            calc
              _ = ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(u+v)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [(Finset.mem_filter.mp ha).2.1, (Finset.mem_filter.mp ha).2.2]
              _ = _ := by simp
          _ ≤ (2:ℝ)^(2*d*(u+v)) * (1/2:ℝ)^(5*d*(u+v)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          _ = _ := by
            have he : 5*d*(u+v)=2*d*(u+v)+3*d*(u+v) := by ring
            rw [he, hcancel]
    _ ≤ 1 := DyadicError.finite_dyadic_error_le_one d hd

omit [Finite W] [Fintype (W →ₗ[F2] V)] in
theorem incident_pair_weight_le_one (X : W →ₗ[F2] V) (d : ℕ)
    (hd : 1 ≤ d) (hX : finrank F2 X.range ≤ 2*d) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
          finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
      then (1/2:ℝ)^(5*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) else 0) ≤ 1 := by
  let i (p : Submodule F2 V × Submodule F2 W) := finrank F2 p.1
  let j (p : Submodule F2 V × Submodule F2 W) := finrank F2 (W ⧸ p.2)
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧ i p ≤ d ∧ j p ≤ d
  let s := Finset.univ.filter good
  have hs (p) (hp : p ∈ s) : good p := (Finset.mem_filter.mp hp).2
  have hbound : ∀ p ∈ s, i p ≤ d ∧ j p ≤ d := by
    intro p hp
    exact (hs p hp).2.2.2
  have hzero : ∀ p ∈ s, ¬(i p=0 ∧ j p=0) := by
    intro p hp hz
    apply (hs p hp).1
    apply (pairDimension_eq_zero_iff p).mp
    exact Nat.add_eq_zero_iff.mpr hz
  have hquot : finrank F2 (W ⧸ X.ker) ≤ 2*d := by
    have hq := X.ker.finrank_quotient_add_finrank
    have hr := X.finrank_range_add_finrank_ker
    omega
  have hcount (u v : ℕ) : (s.filter (fun p => i p=u ∧ j p=v)).card ≤ 2^(2*d*(u+v)) := by
    let t := s.filter (fun p => i p=u ∧ j p=v)
    let LA := {A : Submodule F2 V // A ≤ X.range ∧ finrank F2 A=u}
    let LB := {B : Submodule F2 W // X.ker ≤ B ∧ finrank F2 (W ⧸ B)=v}
    let code (p : ↥t) : LA × LB := by
      have hp := Finset.mem_filter.mp p.property
      have hg := hs p.val hp.1
      exact (⟨p.val.1, hg.2.1, hp.2.1⟩, ⟨p.val.2, hg.2.2.1, hp.2.2⟩)
    have hi : Function.Injective code := by
      intro p q h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : LA × LB => z.1.val) h
      · exact congrArg (fun z : LA × LB => z.2.val) h
    have hc : t.card ≤ Nat.card (LA × LB) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Nat.card_le_card_of_injective code hi
    calc
      _ ≤ Nat.card (LA × LB) := hc
      _ = Nat.card LA * Nat.card LB := Nat.card_prod _ _
      _ ≤ 2^((2*d)*u) * 2^((2*d)*v) := Nat.mul_le_mul
        (card_lower_rank_le X.range (2*d) u hX)
        (card_upper_codim_le X.ker (2*d) v hquot)
      _ = _ := by rw [← pow_add]; congr 1; ring
  simpa only [s, Finset.sum_filter, good, i, j] using
    finite_pair_level_sum s i j d hd hbound hzero hcount

theorem mobius_sq (i : ℕ) : (mobius i)^2 = (2:ℝ)^(2*i.choose 2) := by
  have hs : ((-1:ℝ)^i)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
    norm_num
  unfold mobius
  rw [mul_pow, hs, one_mul, ← pow_mul, Nat.mul_comm]

private theorem twice_choose_two_le_square (i : ℕ) : 2*i.choose 2 ≤ i*i := by
  induction i with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem mobius_pair_sq_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 ≤ (2:ℝ)^(d*(i+j)) := by
  have he : 2*i.choose 2 + 2*j.choose 2 ≤ d*(i+j) := by
    calc
      _ ≤ i*i+j*j := Nat.add_le_add (twice_choose_two_le_square i)
        (twice_choose_two_le_square j)
      _ ≤ d*i+d*j := Nat.add_le_add (Nat.mul_le_mul_right i hi) (Nat.mul_le_mul_right j hj)
      _ = _ := (Nat.mul_add d i j).symm
  have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [mul_pow, mobius_sq, mobius_sq, ← pow_add]
  exact_mod_cast hn

theorem mobius_pair_weight_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 * (1/2:ℝ)^(6*d*(i+j)) ≤ (1/2:ℝ)^(5*d*(i+j)) := by
  calc
    _ ≤ (2:ℝ)^(d*(i+j)) * (1/2:ℝ)^(6*d*(i+j)) :=
      mul_le_mul_of_nonneg_right (mobius_pair_sq_le d i j hi hj) (by positivity)
    _ = _ := by
      have he : 6*d*(i+j) = d*(i+j)+5*d*(i+j) := by ring
      rw [he, pow_add, ← mul_assoc, ← mul_pow]
      norm_num

private theorem exists_nonzero_term {α : Type*} [Fintype α] (f : α → ℝ)
    (h : (∑ x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro x _
  by_contra hx
  exact hn ⟨x,hx⟩

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem filteredCoefficient_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V)
    (h : filteredCoefficient A B a Y ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  have hi : Incidence A B Y := by
    by_contra hn
    exact h (by simp [filteredCoefficient, hn])
  have hay : a Y ≠ 0 := by
    simpa only [filteredCoefficient, ite_eq_left hi] using h
  have hr : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hay (ha Y (Nat.lt_of_not_ge hn))
  have hA := Submodule.finrank_mono hi.1
  have hB := Submodule.finrank_mono hi.2
  have hq := B.finrank_quotient_add_finrank
  have hY := Y.finrank_range_add_finrank_ker
  constructor <;> omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] in
theorem pieceConvolution_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (X : W →ₗ[F2] V)
    (h : pieceConvolution A B a X ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  obtain ⟨Y,hY⟩ := exists_nonzero_term _ h
  apply filteredCoefficient_nonzero_dimensions a d ha A B Y
  intro hz
  apply hY
  rw [hz, zero_mul]

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem rank_add_le (Y Z : W →ₗ[F2] V) :
    finrank F2 (Y+Z).range ≤ finrank F2 Y.range + finrank F2 Z.range := by
  have hle := Submodule.finrank_mono (LinearMap.range_add_le Y Z)
  have heq := Submodule.finrank_sup_add_finrank_inf_eq Y.range Z.range
  omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] in
theorem badConvolution_eq_zero_of_large_rank
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : 2*d < finrank F2 X.range) : badConvolution a X = 0 := by
  by_contra h
  obtain ⟨Y,hY⟩ := exists_nonzero_term _ h
  have hy : a Y ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hz : a (X+Y) ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hry : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hy (ha Y (Nat.lt_of_not_ge hn))
  have hrz : finrank F2 (X+Y).range ≤ d := by
    by_contra hn
    exact hz (ha (X+Y) (Nat.lt_of_not_ge hn))
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  have hr := rank_add_le Y (X+Y)
  rw [hc] at hr
  omega

private theorem scaled_product (c q : ℝ) (n : ℕ) :
    (c * (1/2:ℝ)^n) * ((2:ℝ)^n * q) = c*q := by
  have hc : (1/2:ℝ)^n * (2:ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = c * (((1/2:ℝ)^n * (2:ℝ)^n) * q) := by ring
    _ = _ := by rw [hc, one_mul]

theorem badConvolution_sq_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : finrank F2 X.range ≤ 2*d) :
    badConvolution a X ^ 2 ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
      finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
  let s := Finset.univ.filter good
  let u (p : Submodule F2 V × Submodule F2 W) :=
    signedWeight p * (1/2:ℝ)^(3*d*pairDimension p)
  let v (p : Submodule F2 V × Submodule F2 W) :=
    (2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X
  have heq : badConvolution a X = ∑ p ∈ s, u p * v p := by
    rw [badConvolution_expansion, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg]
      rw [ite_eq_left (show Incidence p.1 p.2 X from ⟨hg.2.1,hg.2.2.1⟩)]
      exact (scaled_product (signedWeight p) (pieceConvolution p.1 p.2 a X)
        (3*d*pairDimension p)).symm
    · rw [ite_eq_right hg]
      by_cases hi : Incidence p.1 p.2 X
      · rw [ite_eq_left hi]
        by_cases hp : p = (⊥,⊤)
        · simp [signedWeight,hp]
        · by_cases hq : pieceConvolution p.1 p.2 a X = 0
          · rw [hq,mul_zero]
          · exact False.elim (hg ⟨hp,hi.1,hi.2,
              pieceConvolution_nonzero_dimensions a d ha p.1 p.2 X hq⟩)
      · rw [ite_eq_right hi]
  have hu : (∑ p ∈ s, u p ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ s, (1/2:ℝ)^(5*d*pairDimension p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hg : good p := (Finset.mem_filter.mp hp).2
        have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
        change (signedWeight p * (1/2:ℝ)^(3*d*pairDimension p))^2 ≤ _
        rw [signedWeight, ite_eq_right hg.1, mul_pow, neg_sq, ← pow_mul, he]
        exact mobius_pair_weight_le d _ _ hg.2.2.2.1 hg.2.2.2.2
      _ ≤ 1 := by
        simpa only [s,Finset.sum_filter,good,pairDimension] using
          incident_pair_weight_le_one X d hd hX
  have hv0 : 0 ≤ ∑ p ∈ s, v p ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : (∑ p ∈ s, v p ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg, ite_eq_left hg.1]
      have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
      change ((2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X)^2 ≤ _
      rw [mul_pow, ← pow_mul, he]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hn : 6*d*pairDimension p ≤ 7*d*pairDimension p :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 6 ≤ 7))
      exact_mod_cast Nat.pow_le_pow_right (n := 2) (by decide) hn
    · rw [ite_eq_right hg]
      split_ifs <;> positivity
  calc
    _ = (∑ p ∈ s, u p * v p)^2 := congrArg (fun x : ℝ => x^2) heq
    _ ≤ (∑ p ∈ s, u p^2) * ∑ p ∈ s, v p^2 := Finset.sum_mul_sq_le_sq_mul_sq s u v
    _ ≤ 1 * ∑ p ∈ s, v p^2 := mul_le_mul_of_nonneg_right hu hv0
    _ = ∑ p ∈ s, v p^2 := one_mul _
    _ ≤ _ := hv

/-- The actual signed bad-convolution estimate of A.1. -/
theorem badConvolution_sq_sum_le_oai
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ X, badConvolution a X ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) *
          (∑ X, pieceConvolution p.1 p.2 a X ^ 2) else 0 := by
  calc
    _ ≤ ∑ X, ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hX : finrank F2 X.range ≤ 2*d
      · exact badConvolution_sq_le a d hd ha X hX
      · rw [badConvolution_eq_zero_of_large_rank a d ha X (Nat.lt_of_not_ge hX), zero_pow (by decide)]
        apply Finset.sum_nonneg
        intro p _
        split_ifs <;> positivity
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = (⊥,⊤)
      · simp [hp]
      · simp [hp,pairDimension,Finset.mul_sum]

end UniqueGamesTheorem.Appendix.BadConvolution

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le_oai.{u_1, u_2}
