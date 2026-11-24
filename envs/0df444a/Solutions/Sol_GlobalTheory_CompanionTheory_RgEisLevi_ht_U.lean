-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.ht_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:19.535663+00:00
-- url     : https://prove2.me/submissions/439d1060-d5a0-4912-8bed-62f5d4e28649

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_isClosed_uQ

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
variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) [T2Space (A.U ε ι)]
    (hK : IsCompact (A.uK ε ι : Set (A.U ε ι))) (s : Set ι) (hI : Iwa (A.uQ ε s) (A.uK ε ι))
    (p : A.U ε ι) (hp : p ∈ A.uQ ε s) (k : A.U ε ι) (hk : k ∈ A.uK ε ι) :
    A.uH ε s (p * k) = A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) := by
  have hb := hB E R A hA.toGoodL (ι ⊕ ι) (Sum.inl '' s)
  have hc : ContinuousOn (fun p : A.U ε ι => bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) (A.uQ ε s : Set (A.U ε ι)) :=
    hb.2.2.1.comp continuous_subtype_val.continuousOn fun x hx => hx
  have hv : ∀ p ∈ A.uQ ε s, p ∈ A.uK ε ι → A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) = 0 :=
    fun p hp hk => hb.2.2.2.2.1 p.1 (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hk)
  exact (hE (A.U ε ι) (A.uK ε ι) (A.uK ε ι) (A.uQ ε s) (fun p => A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1)) hK
    (isClosed_uQ A ε s hb.1) hI
    (fun p hp q hq => by
      have := hb.2.1 p.1 (Subgroup.mem_subgroupOf.1 hp) q.1 (Subgroup.mem_subgroupOf.1 hq)
      simp only [Subgroup.coe_mul, this, hA.lgmul])
    (hA.lgcont.comp_continuousOn hc) hv hv).2 p hp k hk
end GlobalTheory.CompanionTheory.RgEisLevi
