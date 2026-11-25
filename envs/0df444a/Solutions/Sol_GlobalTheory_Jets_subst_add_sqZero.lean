-- Prove2me | solution 1 for GlobalTheory.Jets.subst_add_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:39.072317+00:00
-- url     : https://prove2.me/submissions/2ffb6ff0-c262-4205-b7d0-840eae9f11f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Theorems.Thm_GlobalTheory_Jets_hasSubst_add_sqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_continuous_pderiv_disc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets
open scoped MvPowerSeries.WithPiTopology
namespace GlobalTheory.Jets
theorem _root_.solution {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha0 : ∀ s, IsNilpotent (constantCoeff (a s))) (g : MvPowerSeries σ S) :
    subst (fun s => a s + e * b s) g = subst a g + e * ∑ s, b s * subst a (pderiv S s g) := by
  classical
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := ⟨rfl⟩
  have ha : HasSubst a := hasSubst_of_constantCoeff_nilpotent ha0
  have hb : HasSubst (fun s => a s + e * b s) := hasSubst_add_sqZero a b e he ha0
  have hca : Continuous (subst a : MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst ha
  have hcb : Continuous (subst (fun s => a s + e * b s) :
      MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst hb
  have hs0 : subst a (0 : MvPowerSeries σ S) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ S) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D2 : MvPowerSeries σ S → MvPowerSeries τ S := fun g =>
    subst a g + e * ∑ s, b s * subst a (pderiv S s g)
  have c2 : Continuous D2 :=
    hca.add (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hca.comp (continuous_pderiv_disc _))))
  have hpoly : ∀ p : MvPolynomial σ S,
      subst (fun s => a s + e * b s) (p : MvPowerSeries σ S) = D2 (p : MvPowerSeries σ S) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D2, MvPolynomial.coe_add, subst_add ha, subst_add hb, map_add] at hp hq ⊢
      rw [hp, hq]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    | mul_X p s hp =>
      simp only [D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, subst_mul hb, subst_X hb, hp]
      have hX : ∀ i : σ, pderiv S i (X s : MvPowerSeries σ S) = if i = s then 1 else 0 := by
        intro i
        by_cases h : i = s
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne]
          intro h'
          exact h h'.symm
      have hterm : ∀ i : σ, b i * subst a (pderiv S i ((p : MvPowerSeries σ S) * X s)) =
          (if i = s then b i * subst a (p : MvPowerSeries σ S) else 0) +
            a s * (b i * subst a (pderiv S i (p : MvPowerSeries σ S))) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
      linear_combination (b s * ∑ i, b i * subst a (pderiv S i (p : MvPowerSeries σ S))) * he
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer hcb c2 (funext hpoly)
  exact congrFun this g
end GlobalTheory.Jets
