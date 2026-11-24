-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.leviS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:10:29.663051+00:00
-- url     : https://prove2.me/submissions/83045918-2ea7-4796-b815-91239fdd20d2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piQ_jQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_bdet_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piP_mem_kGL
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_jG_mem_k
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piP_mem_ratGL
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_jG_mem_rat
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_continuous_piQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_continuous_jQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_isClosed_uQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_mem_uQ_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_factor
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_iwa_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_ht_GL
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_ht_U

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution : BdetLaw → ExtLaw → GrpTop → LeviS := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε hI
  obtain ⟨-, -, -, hT2, -, -, hK⟩ := hT E R A hA ι ε
  have hbu := hB E R A hA.toGoodL (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  refine ⟨piQ A ε, jQ A ε hA.σσ, ?_, ?_, iwa_inf A hA ε hI, ?_⟩
  · exact
      { contπ := continuous_piQ A ε
        contι := continuous_jQ A ε hA.σσ hA.σcont
        sect := piQ_jQ A ε hA.σσ
        par :=
          { closed := isClosed_uQ A ε _ hbu.1
            iwa := hI
            ch :=
              { mul := fun _ _ _ _ => by simp
                norm := fun _ _ => by simp
                rat := fun _ _ _ => rfl
                cont := continuousOn_const } }
        triv := fun _ => rfl
        πK := fun q hq => piP_mem_kGL A _ (Subgroup.mem_subgroupOf.1 hq)
        ιK := fun m hm => Subgroup.mem_subgroupOf.2 (jG_mem_k A hA.σO hA.σφ m hm)
        πΓ := fun q hq => piP_mem_ratGL A hA.iinj _ (Subgroup.mem_subgroupOf.1 hq)
        ιΓ := fun m hm => Subgroup.mem_subgroupOf.2 (jG_mem_rat A hA.iinj hA.σi m hm) }
  · intro s
    refine ⟨fun g => ⟨fun h => ⟨h.2, (mem_uQ_iff A ε s ⟨g, h.2⟩).1 h.1⟩,
      fun ⟨hg, h⟩ => ⟨(mem_uQ_iff A ε s ⟨g, hg⟩).2 h, hg⟩⟩, fun q _ => ?_⟩
    have h1 : bdet (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) q.1.1 = Matrix.GeneralLinearGroup.det (piQ A ε q) := by
      rw [bdet_inl Set.univ _ (piQ A ε q) (fun _ _ => rfl)]
      exact (hB E R A hA.toGoodL ι Set.univ).2.2.2.2.2 _
    show ((A.χ (bdet (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) q.1.1) : Circle) : ℂ) =
      1 * ((A.χ (Matrix.GeneralLinearGroup.det (piQ A ε q)) : Circle) : ℂ)
    rw [h1, one_mul]
  · intro s q k hk
    have hinf := iwa_inf A hA ε hI s
    have hIs : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
      obtain ⟨p, hp, k, hk, e⟩ := hinf g
      exact ⟨p, hp.1, k, hk, e⟩
    obtain ⟨p, hp, k', hk', e⟩ := hA.iwa ι s (piQ A ε q)
    obtain ⟨q', h1, h2⟩ := factor A ε hA.σσ q p k' e
    have hjk : ((jQ A ε hA.σσ k').1 : A.U ε ι) ∈ A.uK ε ι :=
      Subgroup.mem_subgroupOf.2 (jG_mem_k A hA.σO hA.σφ k' hk')
    have hq' : q'.1 ∈ A.uQ ε s := (mem_uQ_iff A ε s q').2 (h1 ▸ hp)
    rw [e, ht_GL hB hE A hA s p hp k' hk', h2, mul_assoc,
      ht_U hB hE A hA ε hK s hIs q'.1 hq' _ (mul_mem hjk hk),
      bdet_inl s _ (piQ A ε q') (fun _ _ => rfl), h1]
end GlobalTheory.CompanionTheory.RgEisLevi
