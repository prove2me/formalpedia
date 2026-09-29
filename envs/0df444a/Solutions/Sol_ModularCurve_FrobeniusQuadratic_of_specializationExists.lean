-- Prove2me | solution 1 for ModularCurve.FrobeniusQuadratic.of_specializationExists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ff30fd0e-705d-5205-baea-cba3b900873b

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FrobeniusQuadratic_of_specializationExists

open ModularCurve

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ) (J : Type*)
    [AddCommGroup J] [Module ModularCurve.HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J]
    [SMulCommClass (L ≃ₐ[K] L) ModularCurve.HeckeAlg J]
    (h : ModularCurve.SpecializationExists (K := K) (L := L) N p J) :
    ModularCurve.FrobeniusQuadratic (K := K) (L := L) N p J := by
  intro ℓ hℓ hℓN A hA σ hσ x hx
  obtain ⟨J', _, _, sp, F, hsp, hES⟩ := h ℓ hℓ hℓN A hA
  have htor : ∃ n : ℕ, p ^ n • (σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x) = 0 := by
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have h1 : p ^ n • (σ • σ • x) = 0 := by
      rw [smul_comm, smul_comm (p ^ n), hn, smul_zero, smul_zero]
    have h2 : p ^ n • (heckeGen ⟨ℓ, hℓ⟩ • (σ • x)) = 0 := by
      rw [smul_comm, smul_comm (p ^ n), hn, smul_zero, smul_zero]
    have h3 : p ^ n • ((ℓ : ℕ) • x) = 0 := by
      rw [smul_comm, hn, smul_zero]
    rw [smul_add, smul_sub, h1, h2, h3, sub_zero, add_zero]
  have hker : sp (σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x) = 0 := by
    rw [map_add, map_sub, hsp.frobenius_comm σ hσ, hsp.frobenius_comm σ hσ,
      hsp.hecke_comm, hsp.frobenius_comm σ hσ, map_nsmul]
    exact hES (sp x)
  exact hsp.injective_torsion _ htor hker

end S_ModularCurve_FrobeniusQuadratic_of_specializationExists
end P2MW
export P2MW.S_ModularCurve_FrobeniusQuadratic_of_specializationExists (solution)
