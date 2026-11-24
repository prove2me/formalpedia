-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.eq_zero_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:09:39.006596+00:00
-- url     : https://prove2.me/submissions/17373790-a81e-4937-95dc-12c6079bfbac

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_avg_of_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_isHk_cosetFn
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_hk_cosetFn
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_exists_open_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_finite_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F)))
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W) (T : V →ₗ[ℂ] W)
    (hfix : ∀ v ∈ fixed π K, T v ∈ fixed τ K)
    (hT : ∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v))
    (x : GL ι F →₀ fixed π K) (ha : act π (fixed π K).subtype x = 0)
    (hb : act τ (T ∘ₗ (fixed π K).subtype) x ∈ fixed τ K) :
    act τ (T ∘ₗ (fixed π K).subtype) x = 0 := by
  classical
  obtain ⟨L, hLo, -, hL⟩ := exists_open_sub hKo x.support
  haveI := finite_quot hKc hLo
  letI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hcard : (Fintype.card (K ⧸ L.subgroupOf K) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : avg τ K L (act τ (T ∘ₗ (fixed π K).subtype) x) = T (avg π K L (act π (fixed π K).subtype x)) := by
    simp only [act, Finsupp.coe_lsum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have h1 := hT _ (isHk_cosetFn hKo hKc g (hL g hg)) _ (x g).2
    rw [hk_cosetFn g π (x g).2, hk_cosetFn g τ (hfix _ (x g).2)] at h1
    simpa using h1.symm
  rw [ha, map_zero, map_zero, avg_of_fixed τ K L hb] at key
  exact (smul_eq_zero.1 key).resolve_left hcard
end GlobalTheory.CompanionTheory.HeckeInj
