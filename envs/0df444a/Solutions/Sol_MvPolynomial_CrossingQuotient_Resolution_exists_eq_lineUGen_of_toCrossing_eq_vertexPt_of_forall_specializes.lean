-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7c1697ba-4d44-51d0-ada7-7030eb8aeafd

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionFibrePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MvPolynomial
p2m_export "MvPolynomial" "ext CrossingQuotient.Resolution CrossingQuotient"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "algebraMap_mem_lineVIdeal algebraMap_mem_lineUIdeal chartScheme Resolution V"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "origin lineGen lineUGen lineGen_def lineUGen_def lineUGen_eq_lineGen_succ origin_ne_lineUGen lineUGen_specializes_origin vertexPt eq_origin_or_mem_closure_lineGen_of_toCrossing_eq_vertexPt ι toCrossing toSpec ι_toSpec"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsMaximal] (ht : t ∈ 𝔭)

omit [𝔭.IsMaximal] in

theorem t_mem_toSpec_ι_asIdeal_iff (i : Fin e) (P : chartScheme t) :
    t ∈ ((toSpec t e).base ((ι t e i).base P)).asIdeal ↔ algebraMap W (CrossingQuotient W t) t ∈ P.asIdeal := by
  have h : (toSpec t e).base ((ι t e i).base P) = (ι t e i ≫ toSpec t e).base P := rfl
  rw [h, ι_toSpec]
  exact Iff.rfl

include ht in

theorem exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes (he : 1 ≤ e)
    (o : Resolution t e) (ho : toCrossing t e o = vertexPt t e 𝔭 ht he)
    (hmax : ∀ o' : Resolution t e, o' ⤳ o → t ∈ ((toSpec t e).base o').asIdeal → o' = o) :
    ∃ k : Fin (e - 1), o = lineUGen t e 𝔭 ht ⟨k, by omega⟩ := by
  have htV : ∀ i : Fin e, t ∈ ((toSpec t e).base (lineGen t e 𝔭 ht i)).asIdeal := fun i => by
    rw [lineGen_def, t_mem_toSpec_ι_asIdeal_iff]; exact algebraMap_mem_lineVIdeal t 𝔭 ht ht
  have htU : ∀ i : Fin e, t ∈ ((toSpec t e).base (lineUGen t e 𝔭 ht i)).asIdeal := fun i => by
    rw [lineUGen_def, t_mem_toSpec_ι_asIdeal_iff]; exact algebraMap_mem_lineUIdeal t 𝔭 ht ht
  rcases eq_origin_or_mem_closure_lineGen_of_toCrossing_eq_vertexPt t e 𝔭 ht he o ho with ⟨i, rfl⟩ | ⟨k, hk1, hok⟩
  ·
    exfalso
    exact origin_ne_lineUGen t e 𝔭 ht i i (hmax _ (lineUGen_specializes_origin t e 𝔭 ht i) (htU i)).symm
  ·
    have hgen : lineGen t e 𝔭 ht k = o := hmax _ (specializes_iff_mem_closure.mpr hok) (htV k)
    refine ⟨⟨(k : ℕ) - 1, by omega⟩, ?_⟩
    rw [← hgen]
    have hk' : ((k : ℕ) - 1) + 1 < e := by omega
    rw [lineUGen_eq_lineGen_succ t e 𝔭 ht ⟨(k : ℕ) - 1, by omega⟩ hk']
    congr 1
    exact Fin.ext (by show (k : ℕ) = (k : ℕ) - 1 + 1; omega)

end MvPolynomial.CrossingQuotient.Resolution

open _root_.MvPolynomial _root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes.MvPolynomial _root_.MvPolynomial.CrossingQuotient _root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes.MvPolynomial.CrossingQuotient _root_.MvPolynomial.CrossingQuotient.Resolution _root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes.MvPolynomial.CrossingQuotient.Resolution in
theorem solution
    {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsMaximal] (ht : t ∈ 𝔭) (he : 1 ≤ e)
    (o : Resolution t e) (ho : toCrossing t e o = vertexPt t e 𝔭 ht he)
    (hmax : ∀ o' : Resolution t e, o' ⤳ o → t ∈ ((toSpec t e).base o').asIdeal → o' = o) :
    ∃ k : Fin (e - 1), o = lineUGen t e 𝔭 ht ⟨k, by omega⟩ :=
  exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes t e 𝔭 ht he o ho hmax

end S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes (solution)
