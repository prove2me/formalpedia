-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.sum_local_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:33.447373+00:00
-- url     : https://prove2.me/submissions/05e2d74a-bc5f-45e7-945c-87486f7f24d1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_mem_smallIdeal
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_smallIdeal_isPrime
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_algHom_ext_dense
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_smallIdeal_comp
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_exists_extension
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
    {S : Type} [Fintype S] (P : S → HeightOneSpectrum (𝓞 F)) (hP : Function.Injective P)
    (hS : ∀ I : Ideal (𝓞 F), I.IsPrime → (l : 𝓞 F) ∈ I → ∃ s, (P s).asIdeal = I)
    (K : S → Type) [∀ s, Field (K s)] [∀ s, TopologicalSpace (K s)]
    [∀ s, IsTopologicalRing (K s)] [∀ s, T2Space (K s)] [∀ s, CharZero (K s)]
    [∀ s, Algebra ℚ_[l] (K s)] [∀ s, FiniteDimensional ℚ_[l] (K s)]
    [∀ s, ContinuousSMul ℚ_[l] (K s)] (ι : ∀ s, F →+* K s) (U : ∀ s, Set (K s))
    (hd : ∀ s, DenseRange (ι s)) (hUo : ∀ s, IsOpen (U s))
    (hU : ∀ s x, ι s x ∈ U s ↔ (P s).valuation F x < 1)
    (hpow : ∀ s, ∀ z ∈ U s, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0)) (t : F) :
    ∑ s, Algebra.trace ℚ_[l] (K s) (ι s t) = ((Algebra.trace ℚ F t : ℚ) : ℚ_[l]) := by
  classical
  apply (algebraMap ℚ_[l] (PadicAlgCl l)).injective
  rw [map_sum, map_ratCast]
  have e : ((Algebra.trace ℚ F t : ℚ) : PadicAlgCl l) =
      algebraMap ℚ (PadicAlgCl l) (Algebra.trace ℚ F t) := by simp
  rw [e, trace_eq_sum_embeddings]
  simp_rw [trace_eq_sum_embeddings]
  rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  refine Fintype.sum_bijective
    (fun x : (Σ s, K s →ₐ[ℚ_[l]] PadicAlgCl l) =>
      ((x.2 : K x.1 →+* PadicAlgCl l).comp (ι x.1)).toRatAlgHom) ⟨?_, ?_⟩ _ _ (fun x => rfl)
  · rintro ⟨s, τ⟩ ⟨s', τ'⟩ h
    have h' : (τ : K s →+* PadicAlgCl l).comp (ι s) = (τ' : K s' →+* PadicAlgCl l).comp (ι s') :=
      RingHom.ext fun x => DFunLike.congr_fun h x
    have h1 := smallIdeal_comp (P s) (ι s) (U s) (hU s) (hpow s) τ
    have h2 := smallIdeal_comp (P s') (ι s') (U s') (hU s') (hpow s') τ'
    rw [h', ← h2] at h1
    obtain rfl : s = s' := hP (HeightOneSpectrum.ext h1)
    rw [algHom_ext_dense (ι s) (hd s) τ τ' fun x => DFunLike.congr_fun h' x]
  · intro σ
    obtain ⟨s, hs⟩ := hS (smallIdeal (σ : F →+* PadicAlgCl l)) (smallIdeal_isPrime _) (by
      rw [mem_smallIdeal]
      have : (σ : F →+* PadicAlgCl l) ((l : 𝓞 F) : F) =
          algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
      rw [this, norm_algebraMap']
      exact Padic.norm_p_lt_one)
    obtain ⟨τ, hτ⟩ := exists_extension (P s) (ι s) (U s) (hd s) (hUo s) (hU s) _ hs
    exact ⟨⟨s, τ⟩, AlgHom.ext fun x => hτ x⟩
end GlobalTheory.ResidueCharacterDense
