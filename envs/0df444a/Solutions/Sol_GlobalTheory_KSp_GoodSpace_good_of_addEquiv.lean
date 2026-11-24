-- Prove2me | solution 1 for GlobalTheory.KSp.GoodSpace.good_of_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:40.822328+00:00
-- url     : https://prove2.me/submissions/e6fe2fe1-5489-4855-b5de-4fb23ea191e9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.GoodSpace
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel
namespace GlobalTheory.KSp.GoodSpace
theorem _root_.solution {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
    (f : X ≃+ Y) (hf : Continuous f) (hg : Continuous f.symm) (h : Good Y) : Good X := by
  let H : X ≃ₜ Y := { toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hg }
  haveI := h.grp; haveI := h.t2; haveI := h.lc; haveI := h.sc
  refine ⟨?_, H.isEmbedding.t2Space, H.isClosedEmbedding.locallyCompactSpace, H.isInducing.secondCountableTopology,
    ?_, ?_⟩
  · haveI : ContinuousAdd X := by
      refine ⟨?_⟩
      have : (fun p : X × X => p.1 + p.2) = fun p => f.symm (f p.1 + f p.2) := by
        funext p; simp
      rw [this]; exact hg.comp ((hf.comp continuous_fst).add (hf.comp continuous_snd))
    haveI : ContinuousNeg X := by
      refine ⟨?_⟩
      have : (fun x : X => -x) = fun x => f.symm (-f x) := by funext x; simp
      rw [this]; exact hg.comp hf.neg
    exact {}
  · intro K hK
    obtain ⟨L, hLc, hLo, hKL⟩ := h.large (f '' K) (hK.image hf)
    refine ⟨L.comap f.toAddMonoidHom, ?_, ?_, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · exact hLo.preimage hf
    · intro x hx; exact hKL ⟨x, hx, rfl⟩
  · intro U hU
    have hU' : f.symm ⁻¹' U ∈ 𝓝 (0 : Y) := by
      apply hg.continuousAt.preimage_mem_nhds; simpa using hU
    obtain ⟨L, hLc, hLo, hLU⟩ := h.small _ hU'
    refine ⟨L.comap f.toAddMonoidHom, ?_, hLo.preimage hf, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · intro x hx
      have := hLU hx
      simpa using this
end GlobalTheory.KSp.GoodSpace
