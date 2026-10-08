-- Prove2me | solution 1 for LawlerWCT.RhoMax.max_weight_initial_set_rhoMaximal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:37:44.921308+00:00
-- url     : https://prove2.me/submissions/66cb5a1e-f830-485e-b7e7-8040c970a7a7

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model



namespace LawlerWCT.RhoMax

theorem sep_core {ι : Type*} (N : Finset ι) (w p : ι → ℤ) (pstar : ℤ)
    (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar) (I I' : Finset ι) (hI : I ⊆ N) (hI' : I' ⊆ N)
    (hIne : I.Nonempty) (hI'ne : I'.Nonempty)
    (hne : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ≠
      LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I') :
    1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2 ≤
      |LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I -
        LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I'| := by
  have hP : ∀ J : Finset ι, J ⊆ N → J.Nonempty → 1 ≤ ∑ j ∈ J, p j ∧ ∑ j ∈ J, p j ≤ (N.card : ℤ) * pstar := by
    intro J hJ hJn
    constructor
    · obtain ⟨a, ha⟩ := hJn
      calc (1:ℤ) ≤ p a := (hpb a (hJ ha)).1
        _ ≤ ∑ j ∈ J, p j := Finset.single_le_sum (f := p) (fun j hj => by linarith [(hpb j (hJ hj)).1]) ha
    · calc ∑ j ∈ J, p j ≤ ∑ j ∈ J, pstar := Finset.sum_le_sum (fun j hj => (hpb j (hJ hj)).2)
        _ = J.card * pstar := by simp
        _ ≤ N.card * pstar := by
          obtain ⟨a, ha⟩ := hIne
          have : 0 ≤ pstar := by linarith [(hpb a (hI ha)).1, (hpb a (hI ha)).2]
          have := Finset.card_le_card hJ
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) ‹0 ≤ pstar›
  obtain ⟨h1, h2⟩ := hP I hI hIne
  obtain ⟨h1', h2'⟩ := hP I' hI' hI'ne
  set P := ∑ j ∈ I, p j
  set P' := ∑ j ∈ I', p j
  set W := ∑ j ∈ I, w j
  set W' := ∑ j ∈ I', w j
  have hr : ∀ (a b : ℤ), LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I = (W:ℝ)/(P:ℝ) := by
    intro a b; simp [LawlerWCT.SeriesPar.rho, W, P]
  have hr' : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I' = (W':ℝ)/(P':ℝ) := by
    simp [LawlerWCT.SeriesPar.rho, W', P']
  rw [hr 0 0] at hne ⊢
  rw [hr'] at hne ⊢
  have hPr : (0:ℝ) < P := by exact_mod_cast h1
  have hPr' : (0:ℝ) < P' := by exact_mod_cast h1'
  have hdiff : (W:ℝ)/P - W'/P' = ((W*P' - W'*P : ℤ):ℝ) / ((P:ℝ)*P') := by
    push_cast; field_simp
  have hnz : W*P' - W'*P ≠ 0 := by
    intro h
    apply hne
    rw [div_eq_div_iff hPr.ne' hPr'.ne']
    have : (W:ℝ)*P' - W'*P = 0 := by exact_mod_cast h
    linarith
  have hnum : (1:ℝ) ≤ |((W*P' - W'*P : ℤ):ℝ)| := by
    have : (1:ℤ) ≤ |W*P' - W'*P| := Int.one_le_abs hnz
    exact_mod_cast this
  rw [hdiff, abs_div, abs_of_pos (mul_pos hPr hPr')]
  have hbound : (P:ℝ)*P' ≤ ((N.card:ℝ)*pstar)^2 := by
    have a : (P:ℝ) ≤ N.card * pstar := by exact_mod_cast h2
    have b : (P':ℝ) ≤ N.card * pstar := by exact_mod_cast h2'
    rw [sq]; exact mul_le_mul a b hPr'.le (le_trans hPr.le a)
  calc 1 / ((N.card:ℝ)*pstar)^2 ≤ 1 / ((P:ℝ)*P') := one_div_le_one_div_of_le (mul_pos hPr hPr') hbound
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hPr hPr').le

theorem goal_core {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (w p : ι → ℤ) (wstar pstar : ℤ)
    (hw : ∀ j ∈ N, -wstar ≤ w j ∧ w j ≤ wstar) (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar)
    (Istar : Finset ι)
    (hIstar : LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N Istar)
    (ρ : ℝ)
    (hlo : ρ ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar)
    (hhi : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar ≤
      ρ + 1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2) :
    ∀ I, LawlerWCT.SeriesPar.IsInitialSet G N I → I.Nonempty →
      (∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' →
        trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I' ≤
          trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I) →
      LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N I := by
  intro I hI hIne hmax
  refine ⟨hI, hIne, ?_⟩
  intro I' hI' hI'ne
  by_contra hlt
  push_neg at hlt
  have hpos : ∀ J : Finset ι, J ⊆ N → J.Nonempty → (0:ℝ) < ∑ j ∈ J, (p j : ℝ) := by
    intro J hJ hJn
    exact Finset.sum_pos (fun j hj => by exact_mod_cast (lt_of_lt_of_le one_pos (hpb j (hJ hj)).1)) hJn
  have htw : ∀ J : Finset ι, J ⊆ N → J.Nonempty →
      trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ J =
        (∑ j ∈ J, (p j : ℝ)) * (LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) J - ρ) := by
    intro J hJ hJn
    have := (hpos J hJ hJn).ne'
    unfold trialWeight LawlerWCT.SeriesPar.rho
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
  have hsep := sep_core N w p pstar hpb I I' hI.1 hI'.1 hIne hI'ne hlt.ne
  have hstar := hIstar.2.2 I' hI' hI'ne
  rw [abs_of_neg (by linarith)] at hsep
  have hIle : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ≤ ρ := by linarith
  have h1 := hmax I' hI'
  rw [htw I hI.1 hIne, htw I' hI'.1 hI'ne] at h1
  have a := hpos I hI.1 hIne
  have b := hpos I' hI'.1 hI'ne
  have hIsne := hIstar.2.1
  have h2 := hmax Istar hIstar.1
  rw [htw I hI.1 hIne, htw Istar hIstar.1.1 hIsne] at h2
  have hs := hpos Istar hIstar.1.1 hIsne
  have h3 : 0 ≤ (∑ j ∈ Istar, (p j : ℝ)) * (LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar - ρ) :=
    mul_nonneg hs.le (by linarith)
  have h4 : 0 ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I - ρ := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos a (neg_pos.2 hneg)]
  have hpstar : (0:ℝ) < pstar := by
    obtain ⟨x, hx⟩ := hIne
    exact_mod_cast lt_of_lt_of_le one_pos (le_trans (hpb x (hI.1 hx)).1 (hpb x (hI.1 hx)).2)
  have hcard : (0:ℝ) < N.card := by exact_mod_cast Finset.card_pos.2 ⟨_, hI.1 hIne.choose_spec⟩
  have hδ : 0 < 1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2 := by positivity
  have c : 0 < LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I' - ρ := by linarith
  nlinarith [mul_pos b c, mul_nonneg a.le (sub_nonneg.2 hIle)]

end LawlerWCT.RhoMax

open LawlerWCT.RhoMax


theorem solution {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (w p : ι → ℤ) (wstar pstar : ℤ)
    (hw : ∀ j ∈ N, -wstar ≤ w j ∧ w j ≤ wstar) (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar)
    (Istar : Finset ι)
    (hIstar : LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N Istar)
    (ρ : ℝ)
    (hlo : ρ ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar)
    (hhi : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar ≤
      ρ + 1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2) :
    ∀ I, LawlerWCT.SeriesPar.IsInitialSet G N I → I.Nonempty →
      (∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' →
        trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I' ≤
          trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I) →
      LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N I := by
  exact goal_core N G hGN hacyc w p wstar pstar hw hpb Istar hIstar ρ hlo hhi
