-- Prove2me | solution 1 for GlobalTheory.Reg.Enlarge.clear_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:27.928632+00:00
-- url     : https://prove2.me/submissions/70a140df-91dd-422f-8c12-b9e4963a61af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValue
import Theorems.Thm_GlobalTheory_Reg_Enlarge_exists_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Enlarge
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Reg.Enlarge
theorem _root_.solution {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {r : Ω} (hr : IsIntegral (Algebra.adjoin K gs) r) :
    ∃ κ : O, κ ≠ 0 ∧ ∃ q : Polynomial Ω, q.Monic ∧ q.eval (algebraMap K Ω (algebraMap O K κ) * r) = 0 ∧
      ∀ i, q.coeff i ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hr
  have hex := fun i => exists_den (O := O) gs (p.coeff i).2
  choose d hd0 hd using hex
  set κ : O := ∏ i ∈ Finset.range (p.natDegree + 1), d i with hκdef
  have hκ : κ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i)
  have hκc : ∀ i, algebraMap K Ω (algebraMap O K κ) * ((p.coeff i : Algebra.adjoin K gs) : Ω) ∈ S := by
    intro i
    by_cases hi : i ∈ Finset.range (p.natDegree + 1)
    · rw [hκdef, ← Finset.mul_prod_erase _ _ hi, map_mul, map_mul, mul_comm (algebraMap K Ω (algebraMap O K (d i))),
        mul_assoc]
      exact S.mul_mem (hOS _) (hd i)
    · have : p.coeff i = 0 := p.coeff_eq_zero_of_natDegree_lt (by simp at hi; omega)
      rw [this]
      simp
  set k := algebraMap K Ω (algebraMap O K κ) with hk
  set pm := p.map (algebraMap (Algebra.adjoin K gs) Ω) with hpmdef
  have hpmm : pm.Monic := hpm.map _
  have hdeg : pm.natDegree = p.natDegree := hpm.natDegree_map _
  refine ⟨κ, hκ, pm.scaleRoots k, (monic_scaleRoots_iff k).mpr hpmm, ?_, ?_⟩
  · have h0 : eval₂ (RingHom.id Ω) r pm = 0 := by
      rw [eval₂_id, hpmdef, Polynomial.eval_map]; exact hp
    have := scaleRoots_eval₂_eq_zero (RingHom.id Ω) h0 (s := k)
    rwa [eval₂_id] at this
  · intro i
    rw [coeff_scaleRoots]
    have hci : pm.coeff i = ((p.coeff i : Algebra.adjoin K gs) : Ω) := by
      rw [hpmdef, coeff_map]; rfl
    rcases h : pm.natDegree - i with _ | m
    · rcases (show pm.natDegree ≤ i by omega).lt_or_eq with hlt | heq
      · rw [coeff_eq_zero_of_natDegree_lt hlt]; simp
      · rw [← heq, hpmm.coeff_natDegree]; simp
    · have : pm.coeff i * k ^ (m + 1) = k ^ m * (k * ((p.coeff i : Algebra.adjoin K gs) : Ω)) := by
        rw [hci]; ring
      rw [this]
      exact S.mul_mem (S.pow_mem (hOS κ) m) (hκc i)
end GlobalTheory.Reg.Enlarge
