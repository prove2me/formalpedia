-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.idxN_dual_of_covBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:20.955059+00:00
-- url     : https://prove2.me/submissions/d0aca060-3c40-4504-b87b-a3c9ee0dba6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_exists_max_of_covBy
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_dual_covBy
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (hc : X ⋖ Y) : idxN (dual h X) (dual h Y) = idxN Y X := by
  obtain ⟨P, hP, hPm, hPi⟩ := exists_max_of_covBy hc
  obtain ⟨Q, hQ, hQm, hQi⟩ := exists_max_of_covBy (dual_covBy h hs hn hX hY hc)
  set σ := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range with hσ
  have hσσ : ∀ r, σ (σ r) = r := fun r => genusCovol_hinj (by
    rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])
  let e : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective σ (Function.Involutive.bijective hσσ)
  have hle : P ≤ Q.comap σ := by
    intro r hr
    rw [Ideal.mem_comap, hQm]
    intro x hx
    rw [dualBasic_mem_dual] at hx ⊢
    intro y hy
    have := hx _ ((hPm r).1 hr y hy)
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range] at this
    rw [genusBasic_hsmul_right]
    exact this
  have hPQ : P = Q.comap σ := hP.eq_of_le (Ideal.comap_ne_top σ hQ.ne_top) hle
  have hm : Q = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [hPQ]
    exact (Ideal.map_comap_of_surjective σ e.surjective Q).symm
  rw [hPi, hQi]
  exact (Nat.card_congr (Ideal.quotientEquiv P Q e hm).toEquiv).symm
end GlobalTheory.Mass.DiscOrder
