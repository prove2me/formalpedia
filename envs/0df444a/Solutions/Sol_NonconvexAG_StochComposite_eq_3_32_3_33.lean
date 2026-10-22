-- Prove2me | solution 1 for NonconvexAG.StochComposite.eq_3_32_3_33
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T12:41:22.236642+00:00
-- url     : https://prove2.me/submissions/8e7669c8-46ec-4c40-a962-4ce90d700c50

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace Topology
open GhadimiLan.RSG (E)
open NonconvexAG.StochComposite

-- Ghadimi and Lan, arXiv:1310.3787v1, (3.32)-(3.33), using the three-point
-- optimality principle credited in the pinned v1 bibliography to Ghadimi and Lan [11].
-- Platform formulation: mikedeng1; statement confirmation: Shuze Chen.
-- Alexander Richard Towell (queelius): direction and contribution stewardship.
-- OpenAI Codex: substantial formalization, verification and documentation.
-- Lean/Mathlib contributors: convexity, limits and inner-product infrastructure.

set_option autoImplicit false
namespace ProxThreePointResearch
lemma strong_min_growth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} {F : V → ℝ} {m : ℝ} (hF : StrongConvexOn K m F)
    (v x : V) (hv : v∈K) (hx : x∈K) (hmin : ∀u∈K, F v≤F u) :
    F v + m/2*‖v-x‖^2 ≤ F x := by
  let D := m/2*‖v-x‖^2
  have he : ∀ᶠ t:ℝ in 𝓝[>]0, (1-t)*D ≤ F x-F v := by
    have ht1 : ∀ᶠ t:ℝ in 𝓝[>]0, t<1 :=
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,ht1] with t ht ht1
    have ht0 : 0<t := ht
    have hp := hF.2 hv hx (show 0≤1-t by linarith) ht0.le (by ring)
    have hm := hmin ((1-t)•v+t•x) (hF.1 hv hx (by linarith) ht0.le (by ring))
    have hh : t*((1-t)*D) ≤ t*(F x-F v) := by
      dsimp [D]
      simp only [smul_eq_mul] at hp
      nlinarith [hm.trans hp]
    exact le_of_mul_le_mul_left hh ht0
  have hcont : Continuous (fun t:ℝ => (1-t)*D) := by fun_prop
  have hlim : Tendsto (fun t:ℝ => (1-t)*D) (𝓝[>]0) (𝓝 D) := by
    simpa using hcont.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hbound : D ≤ F x-F v := by simpa using le_of_tendsto hlim he
  dsimp [D] at hbound
  linarith

lemma prox_three_point {n : ℕ} (K : Set (E n)) (X : E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    (v g : E n) (c : ℝ) (hc : 0<c) (x : E n) (hx : x∈K) :
    inner ℝ g (P v g c-x)+X (P v g c) ≤ X x + 1/(2*c)*
      (‖v-x‖^2-‖P v g c-x‖^2-‖P v g c-v‖^2) := by
  let F : E n → ℝ := fun u => inner ℝ g u + ‖u-v‖^2/(2*c)+X u
  have hA : ConvexOn ℝ K
      (fun u => inner ℝ g u-(1/c)*inner ℝ u v+‖v‖^2/(2*c)) := by
    refine ⟨hX.1,?_⟩
    intro a ha b hb r s hr hs hrs
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,smul_eq_mul]
    apply le_of_eq
    have hs' : s=1-r := by linarith
    rw [hs']
    ring
  have hF : StrongConvexOn K (1/c) F := by
    apply strongConvexOn_iff_convex.mpr
    have heq : (fun u => F u-(1/c)/2*‖u‖^2) =
        (fun u => X u+(inner ℝ g u-(1/c)*inner ℝ u v+‖v‖^2/(2*c))) := by
      funext u
      dsimp [F]
      rw [norm_sub_sq_real]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [heq]
    exact hX.add hA
  have hmin := hP v g c hc
  have hh := strong_min_growth hF (P v g c) x hmin.1 hx hmin.2
  dsimp [F] at hh
  rw [norm_sub_rev x v] at hh
  simp only [inner_sub_right]
  have hc2 : 0 < 2*c := by positivity
  field_simp at hh ⊢
  nlinarith
end ProxThreePointResearch

open ProxThreePointResearch

theorem solution {n : ℕ} (gΨ : E n → E n) (K : Set (E n)) (X : E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk := xSeq G P α β lam m x0 ξ
    let xag := xagSeq G P α β lam m x0 ξ
    let xmd := xmdSeq G P α β lam m x0 ξ
    let δ := deltaBar G gΨ P α β lam m x0 ξ
    ∀ω:Ω, ∀k, 1≤k → ∀x∈K,
      inner ℝ (gΨ (xmd k ω)+δ k ω) (xk k ω-x)+X (xk k ω) ≤
        X x+1/(2*lam k)*(‖xk (k-1) ω-x‖^2-‖xk k ω-x‖^2-‖xk k ω-xk (k-1) ω‖^2) ∧
      inner ℝ (gΨ (xmd k ω)+δ k ω) (xag k ω-x)+X (xag k ω) ≤
        X x+1/(2*β k)*(‖xmd k ω-x‖^2-‖xag k ω-x‖^2-‖xag k ω-xmd k ω‖^2) := by
  dsimp only
  intro ω k hk x hx
  have hg : gΨ (xmdSeq G P α β lam m x0 ξ k ω)+deltaBar G gΨ P α β lam m x0 ξ k ω =
      Gbar G P α β lam m x0 ξ k ω := by
    unfold deltaBar
    abel
  have hkx : xSeq G P α β lam m x0 ξ k ω =
      P (xSeq G P α β lam m x0 ξ (k-1) ω) (Gbar G P α β lam m x0 ξ k ω) (lam k) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    rfl
  have hka : xagSeq G P α β lam m x0 ξ k ω =
      P (xmdSeq G P α β lam m x0 ξ k ω) (Gbar G P α β lam m x0 ξ k ω) (β k) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    rfl
  rw [hg,hkx,hka]
  exact ⟨prox_three_point K X hX P hP _ _ _ (hstep.2.2.2.1 k hk) x hx,
    prox_three_point K X hX P hP _ _ _ (hstep.2.2.1 k hk) x hx⟩

#print axioms ProxThreePointResearch.strong_min_growth
#print axioms ProxThreePointResearch.prox_three_point
#print axioms solution
