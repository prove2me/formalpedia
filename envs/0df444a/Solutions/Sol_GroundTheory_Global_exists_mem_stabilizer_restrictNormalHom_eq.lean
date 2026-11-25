-- Prove2me | solution 1 for GroundTheory.Global.exists_mem_stabilizer_restrictNormalHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:34.15537+00:00
-- url     : https://prove2.me/submissions/8499b491-1de1-463d-878e-773a7f5a6ccf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_under_smul
import Theorems.Thm_GroundTheory_Global_restrictNormalHom_restrictScalars
import Theorems.Thm_GroundTheory_Global_restrictScalars_smul_ideal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F))) :
    ∃ σ ∈ MulAction.stabilizer Gal(L/K) Q, AlgEquiv.restrictNormalHom F σ = τ := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  obtain ⟨σ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) L τ
  have : (σ₀ • Q).LiesOver (Q.under (𝓞 F)) :=
    ⟨by rw [under_smul, MulAction.mem_stabilizer_iff.1 hτ]⟩
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under (𝓞 F)) (σ₀ • Q) Q Gal(L/F)
  refine ⟨g.restrictScalars K * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, restrictScalars_smul_ideal, hg]
  · rw [map_mul, restrictNormalHom_restrictScalars, one_mul]
end GroundTheory.Global
