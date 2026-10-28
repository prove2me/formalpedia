-- Prove2me | solution 1 for OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:31:36.319784+00:00
-- url     : https://prove2.me/submissions/edfd4763-1f70-4a60-9fce-4692f68ae675

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_FrobeniusIntermediate_exists_positive_module_rank_transfer
import Theorems.Thm_OAI_Lech_FrobeniusIntermediate_normalizedLength_intermediate_tensor
import Theorems.Thm_OAI_Lech_PerfectDomainStages_frobenius_module_length_tendsto
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum

open TensorProduct


namespace Lech.NormalizedLength
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

lemma map_le_annihilator_baseChange (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul s m =>
    rw [IsScalarTower.algebraMap_smul S r, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, Module.mem_annihilator.mp (hI hr) m,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [smul_add, hx, hy, add_zero]

end Lech.NormalizedLength


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct

lemma finite_extendScalars {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance


instance finite_frobeniusModule (D : Type*) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (n : ℕ) (M : ModuleCat D) [Module.Finite D M] :
    Module.Finite D (FrobeniusModule D p n M) :=
  finite_extendScalars (iterateFrobenius D p n) M
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleTensor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech
variable {A : Type*} [CommRing A]

lemma length_le_quotient_generators {N : Type*} [AddCommGroup N] [Module A N]
    (I : Ideal A) (hI : I ≤ Module.annihilator A N)
    {b : ℕ} (f : (Fin b → A) →ₗ[A] N) (hf : Function.Surjective f) :
    Module.length A N ≤ b * Module.length A (A ⧸ I) := by
  classical
  let P := Submodule.pi Set.univ (fun _ : Fin b => I)
  have hP : P ≤ f.ker := by
    intro x hx
    change f x = 0
    rw [pi_eq_sum_univ x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    exact Module.mem_annihilator.mp (hI (hx i (Set.mem_univ i))) _
  let q := P.liftQ f hP
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact ⟨P.mkQ y,rfl⟩
  calc
    Module.length A N ≤ Module.length A ((Fin b → A) ⧸ P) :=
      Module.length_le_of_surjective q hq
    _ = Module.length A (Fin b → A ⧸ I) :=
      (Submodule.quotientPi (fun _ : Fin b => I)).length_eq
    _ = _ := by simp

open Filter
open scoped Topology


end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped nonZeroDivisors
variable (k : Type*) [Field k]

lemma fin_le_dimension (h : ℕ) : (h : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin h) k) := by
  induction h with
  | zero => exact Order.krullDim_nonneg
  | succ h ih =>
    let e : Fin h ↪ Fin (h+1) := Fin.succEmb h
    let f := (killCompl (R := k) e).toRingHom
    have hf : Function.Surjective f := fun x => ⟨rename e x,killCompl_rename_app x⟩
    have hx : (X 0 : MvPowerSeries (Fin (h+1)) k) ∈ (MvPowerSeries (Fin (h+1)) k)⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hz
        have hc := congrArg (coeff (Finsupp.single 0 1)) hz
        simp at hc)
    have hz : f (X 0) = 0 := by
      apply killCompl_X_eq_zero
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    have hb := ringKrullDim_succ_le_of_surjective f hf hx hz
    calc
      (↑(h+1) : WithBot ℕ∞) = (h : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (MvPowerSeries (Fin h) k) + 1 := add_le_add ih le_rfl
      _ ≤ _ := hb

lemma fin_dimension (h : ℕ) : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
  apply le_antisymm _ (fin_le_dimension k h)
  simpa using dimension_le_variables (Fin h) k

end Lech.PowerSeries


namespace Lech
variable {R S : Type*} [CommRing R] [CommRing S]
lemma ringKrullDim_eq_of_integral_injective (f : R →+* S)
    (hint : f.IsIntegral) (hf : Function.Injective f) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hint⟩
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro p q hpq
    exact Ideal.IsIntegral.comap_lt_comap hpq
  · apply iSup_le
    intro l
    obtain ⟨P,_,hP,hPP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot]
          change RingHom.ker f ≤ _
          rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
          exact bot_le)
    have : P.LiesOver l.head.asIdeal := (Ideal.liesOver_iff _ _).mpr hPP.symm
    obtain ⟨L,hL,_,_⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    simpa only [hL,ringKrullDim] using Order.LTSeries.length_le_krullDim L
end Lech


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))

 

theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top


end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors


namespace Lech
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

end Lech

open scoped BigOperators
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech.FrobeniusIntermediate
variable {D : Type*} [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (B : Subring D) (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)

lemma powerMap_val (x : D) : (powerMap p B e he x : D) = x^(p^e) := rfl

lemma map_radical_primary [IsLocalRing D] [IsLocalRing B] [IsLocalHom B.subtype]
    (H : Ideal D) (hH : H.radical = IsLocalRing.maximalIdeal D) :
    (H.map (powerMap p B e he)).radical = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · apply (IsLocalRing.maximalIdeal.isMaximal B).isPrime.isRadical.radical_le_iff.mpr
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact IsLocalRing.mem_maximalIdeal (powerMap p B e he x) |>.mpr
      (fun hunit => (IsLocalRing.mem_maximalIdeal x).mp
        (hH ▸ Ideal.le_radical hx) (isUnit_of_map_unit (powerMap p B e he) _ hunit))
  · intro b hb
    have hd : (b : D) ∈ H.radical := by
      rw [hH]
      exact show (b : D) ∈ IsLocalRing.maximalIdeal D from
        (show b ∈ (IsLocalRing.maximalIdeal D).comap B.subtype from
          (IsLocalRing.maximalIdeal_comap B.subtype).symm ▸ hb)
    obtain ⟨n,hn⟩ := hd
    refine ⟨n*(p^e),?_⟩
    have hg := Ideal.mem_map_of_mem (powerMap p B e he) hn
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    apply Subtype.ext
    simp only [powerMap_val,Subring.coe_pow,pow_mul]

end Lech.FrobeniusIntermediate


namespace Lech.SeparableOrder
variable (A D K L : Type*) [CommRing A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [Algebra A L]
  [Algebra K L] [Algebra D L] [IsScalarTower A K L] [IsScalarTower A D L]



omit [IsDomain D] in
lemma toField_injective [IsFractionRing D L] : Function.Injective (toField A D K L) := by
  intro x y h
  apply Subtype.ext
  exact IsFractionRing.injective D L (congrArg Subtype.val h)

instance orderFieldFaithful [IsFractionRing D L] :
    FaithfulSMul (order A D K L) (separableClosure K L) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (toField_injective A D K L)

 
lemma order_inherits_units [IsFractionRing D L] {x : D} (hx : x ∈ order A D K L)
    (hu : IsUnit x) : IsUnit (⟨x,hx⟩ : order A D K L) := by
  obtain ⟨u,rfl⟩ := hu
  have hm : (↑(u⁻¹) : D) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (↑(u⁻¹) : D))
    have hi : algebraMap D L (↑(u⁻¹) : D) = (algebraMap D L (↑u : D))⁻¹ := by
      apply mul_left_cancel₀ (show algebraMap D L (↑u : D) ≠ 0 from
        (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr (Units.ne_zero u))
      rw [← map_mul, Units.mul_inv, map_one, mul_inv_cancel₀]
      exact (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr (Units.ne_zero u)
    rw [hi]
    exact Field.isSeparable_inv hx
  exact ⟨⟨⟨↑u,hx⟩,⟨↑(u⁻¹),hm⟩,by ext; exact Units.mul_inv u,
      by ext; exact Units.inv_mul u⟩,rfl⟩

instance orderLocal [IsFractionRing D L] [IsLocalRing D] :
    IsLocalRing (order A D K L) :=
  (order A D K L).toSubring.isLocalRing_of_unit (fun _ hx hu =>
    order_inherits_units A D K L hx hu)

instance orderInclusionLocal [IsFractionRing D L] [IsLocalRing D] :
    IsLocalHom (algebraMap (order A D K L) D) :=
  ⟨fun x hu => order_inherits_units A D K L x.2 hu⟩

variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [FiniteDimensional K L]

omit [IsDomain D] in
 

lemma uniform_power : ∃ n : ℕ, ∀ x : D, x^(p^n) ∈ order A D K L := by
  let E := separableClosure K L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsPurelyInseparable E L := separableClosure.isPurelyInseparable K L
  let : CharP E p := (Algebra.charP_iff K E p).mp inferInstance
  refine ⟨IsPurelyInseparable.exponent E L,fun x => ?_⟩
  change IsSeparable K (algebraMap D L (x^_))
  rw [map_pow]
  obtain ⟨y,hy⟩ := IsPurelyInseparable.exponent_def' E p (algebraMap D L x)
  rw [← hy]
  exact y.2

 

instance orderFraction [IsFractionRing D L] :
    IsFractionRing (order A D K L) (separableClosure K L) := by
  obtain ⟨n,hn⟩ := uniform_power A D K L p
  have hq : 0 < p^n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective D (z : L)
  have hb0 : algebraMap D L b ≠ 0 :=
    (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr
      (nonZeroDivisors.coe_ne_zero ⟨b,hb⟩)
  have hid : algebraMap D L (a*b^(p^n-1)) = (z : L) * algebraMap D L (b^(p^n)) := by
    rw [← hab, map_mul, map_pow, map_pow]
    rw [← Nat.sub_add_cancel hq, pow_succ]
    field_simp
    simp only [Nat.sub_add_cancel hq]
  have ha : a*b^(p^n-1) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (a*b^(p^n-1)))
    rw [hid]
    exact Field.isSeparable_mul z.2 (hn b)
  refine ⟨⟨a*b^(p^n-1),ha⟩, ⟨b^(p^n),hn b⟩, ?_⟩
  apply Subtype.ext
  change (z : L) = algebraMap D L (a*b^(p^n-1)) / algebraMap D L (b^(p^n))
  rw [hid, mul_div_cancel_right₀]
  rw [map_pow]
  exact pow_ne_zero _ hb0

end Lech.SeparableOrder


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_maximal_pow_le (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, (IsLocalRing.maximalIdeal R) ^ a ≤ I := by
  simpa only [hI] using I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing

lemma length_ne_top (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (a * N)) hle

end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusFiniteLength
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct
universe u
lemma extendScalars_annihilator {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map φ ≤ Module.annihilator S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change I.map φ ≤ Module.annihilator S (S ⊗[R] M)
  exact Lech.NormalizedLength.map_le_annihilator_baseChange I hI

lemma finiteLength_of_primary_annihilator {S N : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (I : Ideal S) (hI : I.radical = IsLocalRing.maximalIdeal S)
    (hIN : I ≤ Module.annihilator S N) : IsFiniteLength S N := by
  obtain ⟨b,f,hf⟩ := Module.Finite.exists_fin' S N
  apply Module.length_ne_top_iff.mp
  have hIfin := Lech.Primary.length_ne_top I hI 1
  rw [pow_one] at hIfin
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top b) hIfin)
    (length_le_quotient_generators I hIN f hf)

lemma finiteLength_extendScalars_of_primary {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) (hφ : (I.map φ).radical = IsLocalRing.maximalIdeal S) :
    IsFiniteLength S ((ModuleCat.extendScalars φ).obj M) := by
  have := finite_extendScalars φ M
  exact finiteLength_of_primary_annihilator _ hφ (extendScalars_annihilator φ M I hI)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizationModuleLimit
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Filter
open scoped ENNReal Topology
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

include K L in
 

theorem exists_normalization_frobenius_module_limit_oai
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D))) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
          ((PerfectClosure D p) ⊗[D] M))) := by
  let A := MvPowerSeries (Fin h) k
  let B := order A D K L
  let E := separableClosure K L
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : IsNoetherianRing B.toSubring := inferInstanceAs (IsNoetherianRing B)
  let : IsLocalRing B.toSubring := inferInstanceAs (IsLocalRing B)
  let : IsLocalHom B.toSubring.subtype := inferInstanceAs (IsLocalHom (algebraMap B D))
  let : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
  let : CharP E p := (algebraMap E L).charP (algebraMap E L).injective p
  let : IsLocalHom (algebraMap A B) := ⟨fun x hx =>
    isUnit_of_map_unit (algebraMap A D) x (by
      simpa only [← IsScalarTower.algebraMap_apply A B D] using hx.map (algebraMap B D))⟩
  let : Module.Finite B D := Module.Finite.of_restrictScalars_finite A B D
  have hfb : Function.Injective (algebraMap A B) := by
    intro x y hxy
    exact hf (by simpa only [← IsScalarTower.algebraMap_apply A B D] using
      (congrArg (algebraMap B D) hxy))
  have hresBD : Function.Surjective (algebraMap (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField D)) := by
    intro x
    obtain ⟨a,ha⟩ := hres x
    exact ⟨algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a,
      (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha⟩
  have hresAB : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := by
    intro b
    obtain ⟨a,ha⟩ := hres (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D) b)
    refine ⟨a,(algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)).injective ?_⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha
  have hdim : Lech.dimension B = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A B)
      (Algebra.IsIntegral.isIntegral : (algebraMap A B).IsIntegral) hfb
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast B
    rw [hd] at hh
    exact_mod_cast hh
  have hdimSub : Lech.dimension B.toSubring = h := hdim
  obtain ⟨e,he⟩ := uniform_power A D K L p
  obtain ⟨r,hr,hlim⟩ := Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer p B.toSubring
  refine ⟨r,hr,fun M hM => ?_⟩
  let N := (ModuleCat.extendScalars (Lech.FrobeniusIntermediate.powerMap p B.toSubring e he)).obj M
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := Lech.finiteLength_primary_annihilator hM
  have hN : IsFiniteLength B N :=
    Lech.finiteLength_extendScalars_of_primary (Lech.FrobeniusIntermediate.powerMap p B.toSubring e he)
      M I hIM (Lech.FrobeniusIntermediate.map_radical_primary p B.toSubring e he I hI)
  have ht := frobenius_module_length_tendsto h k B p K E hfb hresAB N hN
  have hout := hlim e he hresBD M hM
    (normalizedLength (Fin h) k p ((PerfectClosure B p) ⊗[B] N))
    (by
      rw [hdimSub]
      apply ht.congr
      intro n
      rfl)
  have heq := Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor
    (Fin h) k D p B e he M
  simp only [Fintype.card_fin] at heq
  rw [heq]
  simpa only [hdim,hdimSub,mul_left_comm] using hout
end Lech.SeparableOrder

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit_oai.{u} := @OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit_oai.{u}
