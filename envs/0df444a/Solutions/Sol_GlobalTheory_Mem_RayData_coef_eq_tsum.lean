-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.coef_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:11.261326+00:00
-- url     : https://prove2.me/submissions/6c3bed16-9549-45a1-b776-f67140402b19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open Classical
namespace GlobalTheory.Mem
namespace RayData
theorem _root_.solution {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (n : ℕ) :
    D.coef χ n = ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      if IsCoprime I.1 (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I.1) : ℂ) else 0 := by
  have := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  rw [tsum_fintype, RayData.coef, ← Finset.sum_filter,
    ← Finset.sum_fiberwise (g := fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} => D.cls I.1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (χ c : ℂ)) (fun I hI => by
    rw [(Finset.mem_filter.1 hI).2]), Finset.sum_const, nsmul_eq_mul, mul_comm, RayData.cnt]
  congr 2
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun I => ⟨⟨I.1, I.2.2.1⟩, by simp [I.2.1, I.2.2.2]⟩
      invFun := fun I => ⟨I.1.1, by
        have := I.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact ⟨this.1, I.1.2, this.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end RayData
end GlobalTheory.Mem
