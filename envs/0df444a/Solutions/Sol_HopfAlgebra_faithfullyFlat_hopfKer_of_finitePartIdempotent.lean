-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_hopfKer_of_finitePartIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/28d010a5-f95e-561a-aaa5-1c0dc2f61dce

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_Module_FaithfullyFlat_of_isLocalized_span
import Theorems.Thm_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent
import Theorems.Thm_HopfAlgebra_faithfullyFlat_quotient_span_one_sub_orbitIdempotent_baseChange_of_finitePartIdempotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_finitePartIdempotent
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false

open scoped TensorProduct

namespace FltWs11
namespace S53

theorem ff_quotient_of_eq {B : Type*} [CommRing B] (H : Type*) [CommRing H] [Algebra B H]
    {I J : Ideal B} (hIJ : I = J)
    (h : Module.FaithfullyFlat (B ⧸ J) ((B ⧸ J) ⊗[B] H)) :
    Module.FaithfullyFlat (B ⧸ I) ((B ⧸ I) ⊗[B] H) := by
  subst hIJ
  exact h

theorem faithfullyFlat_of_corners {B : Type*} [CommRing B] (H : Type*) [CommRing H] [Algebra B H]
    (fB : B) (hfB : IsIdempotentElem fB)
    (hF : Module.FaithfullyFlat (B ⧸ Ideal.span {fB}) ((B ⧸ Ideal.span {fB}) ⊗[B] H))
    (hP : Module.FaithfullyFlat (B ⧸ Ideal.span {1 - fB}) ((B ⧸ Ideal.span {1 - fB}) ⊗[B] H)) :
    Module.FaithfullyFlat B H := by
  classical
  have hfB' : IsIdempotentElem (1 - fB) := hfB.one_sub

  let s : Set B := {fB, 1 - fB}
  have hspan : Ideal.span s = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : fB ∈ Ideal.span s := Ideal.subset_span (Set.mem_insert _ _)
    have h2 : (1 - fB) ∈ Ideal.span s := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have := Ideal.add_mem _ h1 h2
    rwa [add_sub_cancel] at this
  have hidem : ∀ r : s, IsIdempotentElem r.1 := by
    rintro ⟨r, hr⟩
    show IsIdempotentElem r
    rcases hr with rfl | hr
    · exact hfB
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      exact hfB'

  let Rₛ : s → Type _ := fun r => B ⧸ Ideal.span {1 - r.1}
  letI : ∀ r : s, IsLocalization.Away r.1 (Rₛ r) := fun r =>
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem r)
  let Mₛ : s → Type _ := fun r => (Rₛ r) ⊗[B] H
  let g : ∀ r : s, H →ₗ[B] Mₛ r := fun r => TensorProduct.mk B (Rₛ r) H 1
  haveI : ∀ r : s, IsLocalizedModule.Away r.1 (g r) := fun r =>
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r.1) (Rₛ r) (g r)).mpr
      (TensorProduct.isBaseChange B H (Rₛ r))
  refine Module.FaithfullyFlat.of_isLocalized_span s hspan Rₛ Mₛ g (fun r => ?_)

  obtain ⟨r, hr⟩ := r
  rcases hr with rfl | hr
  · exact hP
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ff_quotient_of_eq H (by rw [sub_sub_cancel]) hF

end FltWs11.S53

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
        Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H :=
  FltWs11.S53.faithfullyFlat_of_corners H (⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc)) (Subtype.ext hf)
    (HopfAlgebra.faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent
      R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee' f hf hfK hfe hmin)
    (HopfAlgebra.faithfullyFlat_quotient_span_one_sub_orbitIdempotent_baseChange_of_finitePartIdempotent
      R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee' f hf hfK hfe hmin)

end S_HopfAlgebra_faithfullyFlat_hopfKer_of_finitePartIdempotent
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_finitePartIdempotent (solution)
