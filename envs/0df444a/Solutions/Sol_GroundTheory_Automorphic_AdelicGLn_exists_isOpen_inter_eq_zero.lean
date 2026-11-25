-- Prove2me | solution 1 for GroundTheory.Automorphic.AdelicGLn.exists_isOpen_inter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:46.135601+00:00
-- url     : https://prove2.me/submissions/89f1494d-7c94-4821-9f2f-38f6a17978fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Theorems.Thm_GroundTheory_Global_discreteTopology_principalSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.AdelicGLn
variable (K : Type*) [Field K] [NumberField K] (n : ℕ)
namespace GroundTheory.Automorphic.AdelicGLn
theorem _root_.solution :
    ∃ V : Set 𝔸[K], IsOpen V ∧ (0 : 𝔸[K]) ∈ V ∧ ∀ k : K, algebraMap K 𝔸[K] k ∈ V → k = 0 := by
  have := GroundTheory.Global.discreteTopology_principalSubgroup K
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1
    (isOpen_discrete ({0} : Set (NumberField.AdeleRing.principalSubgroup (𝓞 K) K)))
  refine ⟨V, hVo, ?_, fun k hk => ?_⟩
  · have : (0 : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈ Subtype.val ⁻¹' V := by
      rw [hV]; rfl
    exact this
  · have : (⟨algebraMap K 𝔸[K] k, ⟨k, rfl⟩⟩ : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈
        Subtype.val ⁻¹' V := hk
    rw [hV, Set.mem_singleton_iff, Subtype.ext_iff] at this
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (this.trans (map_zero _).symm)
end GroundTheory.Automorphic.AdelicGLn
