-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.eventually_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:28.407318+00:00
-- url     : https://prove2.me/submissions/d64bb621-d73a-4fbd-8e3e-88e5d3321de4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_ev_int
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_repr_one_tmul
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ y z : Fv F v ⊗[F] E, y ∈ Lv b v → z ∈ Lv b v → y * z ∈ Lv b v := by
  have hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l =>
      Filter.eventually_all.2 fun m => ev_int _
  filter_upwards [hc] with v hv y z hy hz m
  have hyz : y * z = ∑ k, ∑ l,
      ((Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        (Algebra.TensorProduct.basis (Fv F v) b).repr z l) • ((1 : Fv F v) ⊗ₜ[F] (b k * b l)) := by
    conv_lhs =>
      rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y,
        ← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hyz]
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
    repr_one_tmul, smul_eq_mul]
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hy k) (hz l)) (hv k l m)
end GlobalTheory.CompanionTheory.SW.HProj
