-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_far_mass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-19T06:24:51.466201+00:00
-- url     : https://prove2.me/submissions/8af094ca-1c01-471b-a9b1-3deee69128ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_width_admissible
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_odd_count_bound
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_empirical_moment_bound
set_option autoImplicit false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.RegevSketch

private theorem intersectMassLower {α : Type} (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : HasSum w 1) (P Q : α → Prop) (a b : ℝ)
    (hP : (∑' x, w x * (@ite ℝ (¬ P x) (Classical.propDecidable _) 1 0)) ≤ a)
    (hQ : (∑' x, w x * (@ite ℝ (¬ Q x) (Classical.propDecidable _) 1 0)) ≤ b) :
    1 - (a + b) ≤ ∑' x, w x * (@ite ℝ (P x ∧ Q x) (Classical.propDecidable _) 1 0) := by
  let mask (S : α → Prop) (x : α) : ℝ := w x * (if S x then 1 else 0)
  have sm (S : α → Prop) : Summable (mask S) :=
    hs.summable.of_nonneg_of_le (fun x => by by_cases hx : S x <;> simp [mask,hx,hw])
      (fun x => by by_cases hx : S x <;> simp [mask,hx,hw])
  let F := mask (fun x => P x ∧ Q x)
  let U := mask (fun x => ¬ P x)
  let V := mask (fun x => ¬ Q x)
  have hh (x : α) : w x ≤ (F x + U x) + V x := by
    by_cases p : P x <;> by_cases q : Q x <;> simp [F,U,V,mask,p,q,hw]
  have ht := hs.summable.tsum_le_tsum hh (((sm _).add (sm _)).add (sm _))
  rw [hs.tsum_eq, Summable.tsum_add ((sm _).add (sm _)) (sm _),
      Summable.tsum_add (sm _) (sm _)] at ht
  change 1 ≤ (∑' x, F x) + (∑' x, U x) + (∑' x, V x) at ht
  change (∑' x, U x) ≤ a at hP
  change (∑' x, V x) ≤ b at hQ
  change 1 - (a + b) ≤ ∑' x, F x
  linarith

private theorem coefficientMass_nonnegative_local {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℝ) (z : Fin n → ℤ) : 0 ≤ coefficientMass B r z := by
  unfold coefficientMass
  exact div_nonneg (Real.exp_pos _).le (tsum_nonneg (fun _ => (Real.exp_pos _).le))


theorem _root_.solution :
    ∃ C k n₀ : ℕ, 1 ≤ C ∧ ∀ n ≥ n₀, 1 ≤ n →
    ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    ((C : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ)+2)^k) * δ < lam1 B →
    let m := (n+1)^3
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    let E (i : Fin n) (p : Fin m → Fin n → ℤ) : Prop :=
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * ((D i).mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * ((H i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
    ∀ i, (D i).det ≠ 0 ∧ 0 < r i ∧ dgsThreshold (D i) ≤ (r i : ℝ) ∧
      1 - 1/(16*((n : ℝ)+1)) ≤ ∑' p : Fin m → Fin n → ℤ,
        (∏ j, coefficientMass (D i) (r i) (p j)) * (@ite ℝ (E i p) (Classical.propDecidable _) 1 0) := by
  obtain ⟨C,k,N₀,hC,hgeom⟩ := dual_parity_width_admissible
  obtain ⟨N₁,hodd⟩ := dual_parity_odd_count_bound
  obtain ⟨N₂,hmoment⟩ := dual_parity_empirical_moment_bound
  refine ⟨C,k,max N₀ (max N₁ N₂), hC, ?_⟩
  intro n hn hnpos B hB δ hδ hfar
  dsimp only
  intro i
  have hn₀ : N₀ ≤ n := (le_max_left ..).trans hn
  have hn₁ : N₁ ≤ n := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hn₂ : N₂ ≤ n := (le_max_right ..).trans ((le_max_right ..).trans hn)
  let H : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
  let D := H.adjugate.transpose
  let r : ℚ := (Int.natAbs H.det : ℚ) / (100 * δ)
  let m := (n+1)^3
  obtain ⟨heps,hall⟩ := hgeom n hn₀ hnpos B hB δ hδ hfar
  obtain ⟨hH,hD,hr,hthreshold,hsmooth⟩ := hall i
  change H.det ≠ 0 at hH
  change D.det ≠ 0 at hD
  change 0 < r at hr
  change RegevLWE.GaussConv.smoothingParam (inputModule D) (smoothingError n) ≤ (r : ℝ)/2 at hsmooth
  obtain ⟨hnorm,hpar⟩ := hodd n hn₁ hnpos D hD r (by exact_mod_cast hr) heps hsmooth
  have hcov := hmoment n hn₂ hnpos D hD H.det δ hH hδ
  refine ⟨hD,hr,hthreshold,?_⟩
  let w (p : Fin m → Fin n → ℤ) := ∏ j, coefficientMass D r (p j)
  let P (p : Fin m → Fin n → ℤ) := m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card
  let Q (p : Fin m → Fin n → ℤ) := ∀ x : Fin n → ℤ,
    64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
      (m : ℚ) * (H.det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
  let e : ℝ := 1/(32*((n : ℝ)+1))
  have hw (p : Fin m → Fin n → ℤ) : 0 ≤ w p :=
    Finset.prod_nonneg (fun j _ => coefficientMass_nonnegative_local D r (p j))
  have hgood := intersectMassLower w hw hnorm P Q e e (hpar i) hcov
  have he : e+e = 1/(16*((n:ℝ)+1)) := by
    have hnreal : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    dsimp [e]
    field_simp
    <;> ring
  rw [he] at hgood
  exact hgood

end InfoLossLAR.WorstCase.RegevSketch
