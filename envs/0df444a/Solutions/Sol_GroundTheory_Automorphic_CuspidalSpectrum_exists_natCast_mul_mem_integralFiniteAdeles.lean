-- Prove2me | solution 1 for GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_mem_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:52.550821+00:00
-- url     : https://prove2.me/submissions/1036362b-72f0-449f-84f5-271ada92c686

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_pos_natCast_mul_isIntegral
import Theorems.Thm_GroundTheory_Global_algebraMap_integers_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Automorphic.CuspidalSpectrum
theorem _root_.solution (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ c : ℕ, ((c + 1 : ℕ) : FiniteAdeleRing (𝓞 K) K) * a ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles a
  obtain ⟨c, hc0, hint⟩ := exists_pos_natCast_mul_isIntegral K k
  refine ⟨c - 1, ?_⟩
  rw [Nat.sub_add_cancel hc0]
  have h1 : algebraMap K (FiniteAdeleRing (𝓞 K) K) ((c : K) * k) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
    GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles K ⟨_, hint⟩
  have h2 : ((c : ℕ) : FiniteAdeleRing (𝓞 K) K) *
      (a - algebraMap K (FiniteAdeleRing (𝓞 K) K) k) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
    Subring.mul_mem _ (natCast_mem _ _) hk
  have : ((c : ℕ) : FiniteAdeleRing (𝓞 K) K) * a =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) ((c : K) * k) +
        ((c : ℕ) : FiniteAdeleRing (𝓞 K) K) * (a - algebraMap K (FiniteAdeleRing (𝓞 K) K) k) := by
    rw [map_mul, map_natCast]
    ring
  rw [this]
  exact Subring.add_mem _ h1 h2
end GroundTheory.Automorphic.CuspidalSpectrum
