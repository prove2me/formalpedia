-- Prove2me | solution 1 for GlobalTheory.nabValN_lower_bound_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:29.173827+00:00
-- url     : https://prove2.me/submissions/7449636f-f7f2-4987-b0e7-6dfab65d46a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNLowerBoundBaseChange
import Theorems.Thm_GlobalTheory_T_exists_finset_nabValN_eq_sum_coeff_mul_monomial
import Theorems.Thm_GlobalTheory_exists_integral_combination_of_mem_HaO
import Theorems.Thm_GlobalTheory_nabValN_bilinear
import Theorems.Thm_GlobalTheory_nabValN_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (ι : T.Fr →+* C) (R : Subring C), (∀ x, x ∈ R ↔ ((0 : ℝ) : WithTop ℝ) ≤ v x) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) → ∀ (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB T.Fr d O) (B' : FB C d O), (∀ i, B'.G.F i = MvPowerSeries.map ι (B.G.F i)) → (∀ a i, B'.A.act a i = MvPowerSeries.map ι (B.A.act a i)) → ∀ (h : PS T.Fr 2 d), MvPowerSeries.constantCoeff h = 0 → ∀ (w0 : O) (m : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) [Fintype (Letter Ty r n)] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (cp : Letter Ty r n → Fin n) (u : Letter Ty r n → Fin d → T.Fr) (ν : WithBot (WithTop ℝ)), (∀ P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a, ∀ f : PS T.Fr n d, IsIntPS T f → ν ≤ (WithBot.some (v (ι (nabValN B T.Fr h w0 m f cp u P))) : WithBot (WithTop ℝ))) → ∀ P ∈ HaO r n C R cc isX a, ∀ f : PS C n d, (∀ μ, ((0 : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff μ f)) → ν ≤ (WithBot.some (v (nabValN B' C (MvPowerSeries.map ι h) w0 m f cp (fun l j => ι (u l j)) P)) : WithBot (WithTop ℝ)) := by
  intro T C _ _ v ι R hR hV d O _ _ B B' hG hA h hh w0 m Ty _ r n _ cc isX a cp u ν hν P hP f hf
  obtain ⟨s, c, Q, hc, hQ, rfl⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n T.V T.Fr C ι R
    (fun x => (hR _).2 (hV x)) cc isX a P hP
  obtain ⟨-, -, hadd, hsm⟩ := GlobalTheory.nabValN_bilinear C d O B' (MvPowerSeries.map ι h) w0 m n
    (Letter Ty r n) cp (fun l j => ι (u l j))
  have hsum : ∀ (g : PS C n d) (F : Fin s → MvPolynomial (Letter Ty r n) C) (S : Finset (Fin s)),
      nabValN B' C (MvPowerSeries.map ι h) w0 m g cp (fun l j => ι (u l j)) (∑ j ∈ S, F j)
        = ∑ j ∈ S, nabValN B' C (MvPowerSeries.map ι h) w0 m g cp (fun l j => ι (u l j)) (F j) := by
    intro g F S
    classical
    induction S using Finset.induction_on with
    | empty =>
      have := hsm 0 g 0
      simpa using this
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd, ih]
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial C d O B' (MvPowerSeries.map ι h) w0 m n
    (Letter Ty r n) cp (fun l j => ι (u l j))
    (∑ j, MvPolynomial.C (c j) * MvPolynomial.map ι (Q j))
  rw [hS f]
  induction ν using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe w =>
    refine WithBot.coe_le_coe.2 ?_
    refine v.map_le_sum fun μ _ => ?_
    rw [v.map_mul, hsum]
    refine le_trans ?_ (le_add_of_nonneg_left (by simpa using hf μ))
    refine v.map_le_sum fun j _ => ?_
    rw [hsm, v.map_mul]
    refine le_trans ?_ (le_add_of_nonneg_left (by simpa using (hR _).1 (hc j)))
    have hmon : (MvPowerSeries.monomial μ (1 : C) : PS C n d)
        = MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr) : PS T.Fr n d) := by
      rw [MvPowerSeries.map_monomial, map_one ι]
    rw [hmon, GlobalTheory.nabValN_map T.Fr C ι d O B B' hG hA h hh w0 m n _ (Letter Ty r n) cp u (Q j)]
    refine WithBot.coe_le_coe.1 (hν (Q j) (hQ j) _ ?_)
    intro ρ
    classical
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
end GlobalTheory
