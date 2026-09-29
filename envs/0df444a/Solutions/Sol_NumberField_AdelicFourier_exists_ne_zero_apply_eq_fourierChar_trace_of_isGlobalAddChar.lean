-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/50125ded-6ad2-59c7-acf8-164588e4058c

import Theorems.Thm_AddChar_exists_continuousLinearMap_fourierChar_eq
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Fourier.FourierTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.NumberField MeasureTheory"
open scoped RestrictedProduct
open scoped FourierTransform
p2m_open "Real P2MW.S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.Real"

open scoped FourierTransform
p2m_open "Real P2MW.S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.Real"

namespace AddChar
p2m_export "AddChar" "map_zero_eq_one coe_one ext compAddMonoidHom map_add_eq_mul' coe_eq_one toAddMonoidHom map_add_eq_mul map_zero_eq_one' toFun one_apply exists_continuousLinearMap_fourierChar_eq"
p2m_open "AddChar"

theorem exists_continuousLinearMap_fourierChar_eq_of_norm_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E ℂ) (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = (𝐞 (l x) : ℂ) := by

  let χ' : AddChar E Circle :=
    { toFun := fun x => ⟨χ x, by simp [Submonoid.unitSphere, hχ1 x]⟩
      map_zero_eq_one' := by ext; simp
      map_add_eq_mul' := fun x y => by ext; simp [map_add_eq_mul] }
  have hχ' : Continuous χ' := by
    refine Continuous.subtype_mk hχ _
  obtain ⟨l, hl⟩ := exists_continuousLinearMap_fourierChar_eq χ' hχ'
  exact ⟨l, fun x => by simpa [χ'] using congrArg ((↑) : Circle → ℂ) (hl x)⟩

theorem exists_fourierChar_bilinForm_eq_of_norm_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hB : B.Nondegenerate)
    (χ : AddChar E ℂ) (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) :
    ∃ t : E, ∀ x, χ x = (𝐞 (B t x) : ℂ) := by
  obtain ⟨l, hl⟩ := exists_continuousLinearMap_fourierChar_eq_of_norm_eq_one χ hχ hχ1
  refine ⟨(B.toDual hB).symm (l : Module.Dual ℝ E), fun x => ?_⟩
  rw [hl x, LinearMap.BilinForm.apply_toDual_symm_apply]
  rfl

end AddChar

section CharLite

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.NumberField NumberField.mixedEmbedding NumberField.AdelicBox AutomorphicForm NumberField.InfinitePlace"

open scoped Classical nonZeroDivisors

namespace Real p2m_export "Real" "fourierChar_apply' fourierChar lattice" end Real
p2m_open_scoped "Real" in

theorem Real.fourierChar_eq_one_iff (r : ℝ) : 𝐞 r = 1 ↔ ∃ n : ℤ, r = n := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * π : ℝ) ≠ 0 := by positivity
    have : 2 * π * r = 2 * π * n := by rw [hn]; ring
    exact mul_left_cancel₀ h2 this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

namespace NumberField p2m_export "NumberField" "InfiniteAdeleRing InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp mixedEmbedding.idealLattice RingOfIntegers mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace_apply InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace AdeleRing RingOfIntegers.coe_ne_zero_iff AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar" namespace InfiniteAdeleRing p2m_export "NumberField.InfiniteAdeleRing" "mixedEmbedding_eq_algebraMap_comp ringEquiv_mixedSpace_apply ringEquiv_mixedSpace" end NumberField.InfiniteAdeleRing
p2m_open_scoped "NumberField NumberField.InfiniteAdeleRing" in

theorem NumberField.InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm
    (K : Type*) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace K

  let g : mixedSpace K → InfiniteAdeleRing K := fun y v =>
    if hv : IsReal v then (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩)
    else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hv)).symm
      (y.2 ⟨v, not_isReal_iff_isComplex.mp hv⟩)
  have hg : Continuous g := by
    refine continuous_pi fun v => ?_
    by_cases hv : IsReal v
    · simp only [g, dif_pos hv]
      exact (IsometryEquiv.continuous _).comp ((continuous_apply _).comp continuous_fst)
    · simp only [g, dif_neg hv]
      exact (IsometryEquiv.continuous _).comp ((continuous_apply _).comp continuous_snd)
  have heg : ∀ y, e (g y) = y := by
    intro y
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · have hw : IsReal (w : InfinitePlace K) := w.2
      simp only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, g, dif_pos hw]
      exact (Completion.isometryEquivRealOfIsReal hw).apply_symm_apply (y.1 w)
    · have hw : ¬ IsReal (w : InfinitePlace K) := not_isReal_iff_isComplex.mpr w.2
      simp only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, g, dif_neg hw]
      exact (Completion.isometryEquivComplexOfIsComplex w.2).apply_symm_apply (y.2 w)
  have : (e.symm : mixedSpace K → InfiniteAdeleRing K) = g := by
    funext y
    apply e.injective
    rw [e.apply_symm_apply, heg]
  rw [this]
  exact hg

theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ a : F, a ≠ 0 ∧ ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
  set V := mixedSpace F
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he_def

  have hmul : ∀ a b : AdeleRing (𝓞 F) F, ψ (a + b) = ψ a * ψ b := fun a b =>
    AddChar.map_add_eq_mul ψ a b
  have hsplit : ∀ z : AdeleRing (𝓞 F) F, ψ z = ψ (z.1, 0) * ψ (0, z.2) := fun z => by
    rw [← hmul]
    congr 1
    exact Prod.ext (by change z.1 = z.1 + 0; rw [add_zero]) (by change z.2 = 0 + z.2; rw [zero_add])
  have hι : ∀ q : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) q)
      = ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
        * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := fun q => by
    rw [← hmul]
    congr 1
    refine Prod.ext ?_ ?_
    · change (algebraMap F (AdeleRing (𝓞 F) F) q).1 = algebraMap F (InfiniteAdeleRing F) q + 0
      rw [add_zero]; rfl
    · change (algebraMap F (AdeleRing (𝓞 F) F) q).2 = 0 + algebraMap F (FiniteAdeleRing (𝓞 F) F) q
      rw [zero_add]; rfl
  have hpair : ∀ A B : FiniteAdeleRing (𝓞 F) F, ψ (0, A + B) = ψ (0, A) * ψ (0, B) := fun A B => by
    rw [← hmul]
    congr 1
    exact Prod.ext (by change (0 : InfiniteAdeleRing F) = 0 + 0; rw [add_zero]) rfl

  let ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hψf_apply : ∀ z, ψf z = ψ (0, z) := fun z => rfl
  have hψf_cont : Continuous ψf :=
    hψ.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_addChar_mul_eq_one F hψf_cont
  have hdF : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd0

  have hψ_inf_fin : ∀ q : F, ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
      * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) = 1 := fun q => by
    rw [← hι]; exact hψ.principalInvariant q

  let χ : AddChar V ℂ :=
    (ψ.compAddMonoidHom (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
      |>.compAddMonoidHom e.symm.toAddMonoidHom
  have hχ_apply : ∀ v, χ v = ψ (e.symm v, 0) := fun v => rfl
  have hχc : Continuous χ := by
    change Continuous (fun v => χ v)
    simp_rw [hχ_apply]
    exact hψ.continuous.comp
      ((InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm F).prodMk continuous_const)
  have hχ1 : ∀ v, ‖χ v‖ = 1 := fun v =>
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _
  obtain ⟨t, ht⟩ := AddChar.exists_fourierChar_bilinForm_eq_of_norm_eq_one
    (Algebra.traceForm ℝ V) (traceForm_mixedSpace_nondegenerate F) χ hχc hχ1
  have hψinf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (𝐞 (Algebra.trace ℝ V (t * e x)) : ℂ) := fun x => by
    have := ht (e x)
    rwa [hχ_apply, RingEquiv.symm_apply_apply, Algebra.traceForm_apply] at this
  have heι : ∀ q : F, e (algebraMap F (InfiniteAdeleRing F) q) = mixedEmbedding F q :=
    fun q => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F (x := q)).symm

  have hint : ∀ a : 𝓞 F, ∃ m : ℤ,
      Algebra.trace ℝ V (t * mixedEmbedding F ((d : F) * a)) = m := fun a => by
    have h1 := hψ_inf_fin ((d : F) * a)
    have h2 : ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * a)) = 1 := by
      rw [map_mul, ← hψf_apply]
      refine hd _ fun v => ?_
      exact algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a
    rw [h2, mul_one, hψinf, heι, Circle.coe_eq_one, Real.fourierChar_eq_one_iff] at h1
    exact h1

  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
    Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdF)
  have htdual : t ∈ (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ V).flip
      (mixedEmbedding.idealLattice F I) : Set V) := by
    change t ∈ LinearMap.BilinForm.dualSubmodule _ _
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [mem_idealLattice] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hq' : q ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F) := by
      simpa [I] using hq
    rw [FractionalIdeal.mem_spanSingleton] at hq'
    obtain ⟨a, rfl⟩ := hq'
    obtain ⟨m, hm⟩ := hint a
    have hflip : ∀ u w : V, (Algebra.traceForm ℝ V).flip u w = Algebra.trace ℝ V (w * u) :=
      fun u w => by
        show Algebra.traceForm ℝ V w u = _
        exact Algebra.traceForm_apply _ _ _
    rw [hflip, Submodule.mem_one]
    refine ⟨m, ?_⟩
    have hq : a • (d : F) = (d : F) * a := by rw [Algebra.smul_def, mul_comm]
    rw [eq_intCast, ← hm, hq, mul_comm t]
  rw [coe_dualSubmodule_flip_traceForm_idealLattice F I] at htdual
  obtain ⟨a₀, -, ha₀t⟩ := htdual

  have ha₀ : a₀ ≠ 0 := by
    rintro rfl
    apply hψ.nontrivial
    have hinf1 : ∀ x : InfiniteAdeleRing F, ψ (x, 0) = 1 := fun x => by
      rw [hψinf, ← ha₀t, map_zero, zero_mul, map_zero, AddChar.map_zero_eq_one, Circle.coe_one]
    have hfinF : ∀ q : F, ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) = 1 := fun q => by
      have := hψ_inf_fin q
      rwa [hinf1, one_mul] at this
    have hfin1 : ∀ z : FiniteAdeleRing (𝓞 F) F, ψ (0, z) = 1 := fun z => by
      obtain ⟨u, hu⟩ := (IsUnit.mk0 (d : F) hdF).map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
      obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F ((u⁻¹).val * z)
      have hz : z = u.val * (algebraMap F _ k + (u⁻¹).val * z) + -(u.val * algebraMap F _ k) := by
        rw [mul_add, ← mul_assoc, Units.mul_inv, one_mul]; ring
      rw [hz, hpair]
      have h1 : ψ (0, u.val * (algebraMap F _ k + (u⁻¹).val * z)) = 1 := by
        rw [hu, ← hψf_apply]; exact hd _ hk
      have h2 : ψ (0, -(u.val * algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) = 1 := by
        rw [hu, ← map_mul, ← map_neg]; exact hfinF _
      rw [h1, h2, one_mul]
    refine AddChar.ext _ _ fun z => ?_
    rw [AddChar.one_apply, hsplit z, hinf1, hfin1, one_mul]

  refine ⟨a₀⁻¹, inv_ne_zero ha₀, fun x => ?_⟩
  rw [hψinf, ← ha₀t, RingEquiv.map_mul, heι, ← mul_assoc, ← (mixedEmbedding F).map_mul,
    mul_inv_cancel₀ ha₀, map_one, one_mul]

end CharLite

end S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar (solution)
