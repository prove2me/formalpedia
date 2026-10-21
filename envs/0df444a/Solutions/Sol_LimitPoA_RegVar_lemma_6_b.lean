-- Prove2me | solution 1 for LimitPoA.RegVar.lemma_6_b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:17:16.977113+00:00
-- url     : https://prove2.me/submissions/00a2cc3c-22ef-4f9b-889a-a106f5519ecb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit
import Definitions.Def_LimitPoA_RegVar_Decomp
import Theorems.Thm_LimitPoA_RegVar_lemma_6_a
import Theorems.Thm_LimitPoA_RegVar_exists_SO_profile
import Theorems.Thm_LimitPoA_RegVar_NE_cost_unique
import Theorems.Thm_KellyStochasticNetworks_wardrop_equilibrium_exists

open Filter Topology LimitPoA.RegVar KellyStochasticNetworks

namespace LimPoA6b

lemma inc_nonneg (Γ : Game) (hΓ : Γ.Standing) (a : Fin Γ.J) (s : Fin Γ.R) : 0 ≤ Γ.inc a s := by
  rcases hΓ.2.1 a s with h | h <;> simp [h]

lemma load_nonneg (Γ : Game) (hΓ : Γ.Standing) {f : Fin Γ.R → ℝ} (hf : ∀ r, 0 ≤ f r)
    (a : Fin Γ.J) : 0 ≤ load Γ f a := by
  unfold load linkFlow
  exact Finset.sum_nonneg fun r _ => mul_nonneg (inc_nonneg Γ hΓ a r) (hf r)

lemma sum_mul_stratCost (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ) (f x : Fin Γ.R → ℝ) :
    (∑ s, x s * stratCost Γ τ f s) = ∑ j, τ j (load Γ f j) * load Γ x j := by
  simp only [stratCost, load, linkFlow, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

lemma cost_nonneg (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) {f : Fin Γ.R → ℝ} (hf : ∀ r, 0 ≤ f r) : 0 ≤ cost Γ τ f :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (load_nonneg Γ hΓ hf a) ((hτ a).2.2 _ (load_nonneg Γ hΓ hf a))

lemma exists_NE (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsNE Γ τ d f := by
  let D : Fin Γ.J → ℝ → ℝ := fun a x => τ a (max x 0)
  have hDc : ∀ a, Continuous (D a) := fun a =>
    (hτ a).1.comp_continuous (continuous_id.max continuous_const) (fun x => le_max_right x 0)
  have hDm : ∀ a, Monotone (D a) := fun a x y hxy =>
    (hτ a).2.1 (Set.mem_Ici.mpr (le_max_right x 0)) (Set.mem_Ici.mpr (le_max_right y 0))
      (max_le_max hxy le_rfl)
  obtain ⟨x, hx⟩ := wardrop_equilibrium_exists Γ.inc Γ.grp D d hΓ.2.1 hDc hDm hd hΓ.2.2.2.2
  refine ⟨x, hx.1, fun r r' h hp => ?_⟩
  have := hx.2 r r' h hp
  have e : ∀ j, D j (linkFlow Γ.inc x j) = τ j (linkFlow Γ.inc x j) := fun j => by
    have hm : max (linkFlow Γ.inc x j) 0 = linkFlow Γ.inc x j :=
      max_eq_left (load_nonneg Γ hΓ hx.1.1 j)
    simp only [D, hm]
  simpa only [e] using this

lemma NECost_eq (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsNE Γ τ d f) :
    NECost Γ τ d = cost Γ τ f := by
  unfold NECost
  have : cost Γ τ '' {f | IsNE Γ τ d f} = {cost Γ τ f} := by
    ext y; constructor
    · rintro ⟨g, hg, rfl⟩; exact Set.mem_singleton_iff.mpr (NE_cost_unique Γ hΓ τ hτ d g f hg hf)
    · intro hy; rw [Set.mem_singleton_iff.mp hy]; exact ⟨f, hf, rfl⟩
  rw [this, csSup_singleton]

lemma SOCost_eq (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ)
    (hf : IsSO Γ τ d f) : SOCost Γ τ d = cost Γ τ f := by
  unfold SOCost
  exact IsLeast.csInf_eq ⟨⟨f, hf.1, rfl⟩, by rintro y ⟨g, hg, rfl⟩; exact hf.2 g hg⟩

lemma NECost_nonneg (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : Fin Γ.Sd → ℝ) : 0 ≤ NECost Γ τ d :=
  Real.sSup_nonneg (by rintro y ⟨g, hg, rfl⟩; exact cost_nonneg Γ hΓ τ hτ hg.1.1)

lemma restrict_nonneg (Γ : Game) (K : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ)
    (hd : ∀ k, 0 ≤ d k) (k : Fin Γ.Sd) : 0 ≤ restrict Γ K d k := by
  unfold restrict; split_ifs
  · exact hd k
  · exact le_rfl

lemma restrictProfile_isProfile (Γ : Game) (K : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    IsProfile Γ (restrict Γ K d) (restrictProfile Γ K f) := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨fun r => ?_, fun σ => ?_⟩
  · unfold restrictProfile; split_ifs
    · exact h1 r
    · exact le_rfl
  · unfold restrictProfile restrict
    by_cases hσ : σ ∈ K
    · rw [if_pos hσ, ← h2 σ]
      refine Finset.sum_congr rfl fun r hr => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [if_pos (hr ▸ hσ)]
    · rw [if_neg hσ]
      refine Finset.sum_eq_zero fun r hr => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [if_neg (hr ▸ hσ)]

lemma cost_restrict_le_joint (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (K : Finset (Fin Γ.Sd)) (f : Fin Γ.R → ℝ) (hf : ∀ r, 0 ≤ f r) :
    cost Γ τ (restrictProfile Γ K f) ≤ jointTotalCost Γ τ K f := by
  have hrp : ∀ r, 0 ≤ restrictProfile Γ K f r := fun r => by
    unfold restrictProfile; split_ifs
    · exact hf r
    · exact le_rfl
  have hle : ∀ a, load Γ (restrictProfile Γ K f) a ≤ load Γ f a := fun a => by
    unfold load linkFlow
    refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (inc_nonneg Γ hΓ a r)
    unfold restrictProfile; split_ifs
    · exact le_rfl
    · exact hf r
  calc cost Γ τ (restrictProfile Γ K f)
      ≤ ∑ a, load Γ (restrictProfile Γ K f) a * τ a (load Γ f a) := by
        refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (load_nonneg Γ hΓ hrp a)
        exact (hτ a).2.1 (Set.mem_Ici.mpr (load_nonneg Γ hΓ hrp a))
          (Set.mem_Ici.mpr (load_nonneg Γ hΓ hf a)) (hle a)
    _ = ∑ s, restrictProfile Γ K f s * stratCost Γ τ f s := by
        rw [sum_mul_stratCost]
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = jointTotalCost Γ τ K f := by
        unfold jointTotalCost restrictProfile
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> simp

lemma joint_sum_eq_cost (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ) {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) (hpart : ∀ k, ∃! u, k ∈ cls u) (f : Fin Γ.R → ℝ) :
    ∑ u, jointTotalCost Γ τ (cls u) f = cost Γ τ f := by
  classical
  unfold jointTotalCost
  rw [Finset.sum_comm]
  have h1 : ∀ s, (∑ u, if Γ.grp s ∈ cls u then f s * stratCost Γ τ f s else 0) =
      f s * stratCost Γ τ f s := by
    intro s
    obtain ⟨u0, hu0, huniq⟩ := hpart (Γ.grp s)
    rw [Finset.sum_eq_single u0]
    · rw [if_pos hu0]
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (huniq b hbm)
    · intro h; exact absurd (Finset.mem_univ u0) h
  rw [Finset.sum_congr rfl fun s _ => h1 s, sum_mul_stratCost]
  unfold cost
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- for large demand on some group, every profile has positive social cost -/
lemma cost_pos (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0) :
    ∃ X : ℝ, ∀ (D : Fin Γ.Sd → ℝ) (k0 : Fin Γ.Sd), X ≤ D k0 →
      ∀ f, IsProfile Γ D f → 0 < cost Γ τ f := by
  classical
  choose x0 hx0 using hnd
  set S : ℝ := ∑ a, x0 a with hS
  refine ⟨(Γ.R : ℝ) * S, fun D k0 hD f hf => ?_⟩
  obtain ⟨h1, h2⟩ := hf
  set F := Finset.univ.filter (fun r => Γ.grp r = k0) with hF
  have hFne : F.Nonempty := by
    obtain ⟨s, hs⟩ := hΓ.2.2.2.2 k0
    exact ⟨s, by simp [hF, hs]⟩
  have hex : ∃ r ∈ F, S ≤ f r := by
    by_contra hcon
    push_neg at hcon
    have hlt : (∑ r ∈ F, f r) < ∑ r ∈ F, S := Finset.sum_lt_sum_of_nonempty hFne hcon
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    have hcard : (F.card : ℝ) ≤ Γ.R := by
      have := Finset.card_filter_le (Finset.univ : Finset (Fin Γ.R)) (fun r => Γ.grp r = k0)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => (hx0 a).1.le
    have := h2 k0
    nlinarith
  obtain ⟨r, -, hr⟩ := hex
  obtain ⟨a, ha⟩ := hΓ.2.2.1 r
  have hla : f r ≤ load Γ f a := by
    unfold load linkFlow
    calc f r = Γ.inc a r * f r := by rw [ha, one_mul]
      _ ≤ ∑ s, Γ.inc a s * f s :=
        Finset.single_le_sum (f := fun s => Γ.inc a s * f s)
          (fun s _ => mul_nonneg (inc_nonneg Γ hΓ a s) (h1 s)) (Finset.mem_univ r)
  have hxa : x0 a ≤ S := Finset.single_le_sum (f := x0) (fun b _ => (hx0 b).1.le) (Finset.mem_univ a)
  have hl : x0 a ≤ load Γ f a := hxa.trans (hr.trans hla)
  have hτpos : 0 < τ a (x0 a) :=
    lt_of_le_of_ne ((hτ a).2.2 _ (hx0 a).1.le) (hx0 a).2.symm
  have hτl : τ a (x0 a) ≤ τ a (load Γ f a) :=
    (hτ a).2.1 (Set.mem_Ici.mpr (hx0 a).1.le) (Set.mem_Ici.mpr ((hx0 a).1.le.trans hl)) hl
  have hterm : 0 < load Γ f a * τ a (load Γ f a) :=
    mul_pos ((hx0 a).1.trans_le hl) (hτpos.trans_le hτl)
  unfold cost
  exact hterm.trans_le (Finset.single_le_sum
    (f := fun b => load Γ f b * τ b (load Γ f b))
    (fun b _ => mul_nonneg (load_nonneg Γ hΓ h1 b) ((hτ b).2.2 _ (load_nonneg Γ hΓ h1 b)))
    (Finset.mem_univ a))

end LimPoA6b

open LimPoA6b

theorem solution (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (d : ℕ → Fin Γ.Sd → ℝ) (hdec : IsDecomposable Γ Finset.univ d)
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) (g : Fin m → ℕ → ℝ)
    (hAD : IsAsymDecomp Γ τ Finset.univ d m cls g) :
    (∀ (n : ℕ) (u : Fin m) (fSO fSOu : Fin Γ.R → ℝ), IsSO Γ τ (d n) fSO →
        IsSO Γ τ (restrict Γ (cls u) (d n)) fSOu →
        cost Γ τ fSOu ≤ cost Γ τ (restrictProfile Γ (cls u) fSO) ∧
          cost Γ τ (restrictProfile Γ (cls u) fSO) ≤ jointTotalCost Γ τ (cls u) fSO) ∧
    (∀ fSO : ℕ → Fin Γ.R → ℝ, (∀ n, IsSO Γ τ (d n) (fSO n)) →
      limsup (fun n => ((PoA Γ τ (d n) : ℝ) : EReal)) atTop =
        limsup (fun n =>
          ((NECost Γ τ (d n) / ∑ u, jointTotalCost Γ τ (cls u) (fSO n) : ℝ) : EReal)) atTop) ∧
    limsup (fun n => ((PoA Γ τ (d n) : ℝ) : EReal)) atTop ≤
      limsup (fun n =>
        ((NECost Γ τ (d n) / ∑ u, SOCost Γ τ (restrict Γ (cls u) (d n)) : ℝ) : EReal)) atTop ∧
    limsup (fun n =>
        ((NECost Γ τ (d n) / ∑ u, SOCost Γ τ (restrict Γ (cls u) (d n)) : ℝ) : EReal)) atTop =
      limsup (fun n => ((PoABar Γ τ cls (d n) : ℝ) : EReal)) atTop := by
  classical
  have hAD0 := hAD
  obtain ⟨-, hclsne, hdisj, hcover, -, -, -⟩ := hAD
  have hdnn : ∀ n k, 0 ≤ d n k := by
    obtain ⟨-, ⟨dI, hreg⟩, -, -⟩ := hdec
    exact hreg.1.1
  have hdinf : ∀ k, Tendsto (fun n => d n k) atTop atTop := fun k =>
    hdec.2.2.1 k (Finset.mem_univ k)
  have hpart : ∀ k, ∃! u, k ∈ cls u := by
    intro k
    obtain ⟨u, hu⟩ := (hcover k).mp (Finset.mem_univ k)
    refine ⟨u, hu, fun v hv => ?_⟩
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj v u hne) hv hu
  have P1 : ∀ (n : ℕ) (u : Fin m) (fSO fSOu : Fin Γ.R → ℝ), IsSO Γ τ (d n) fSO →
      IsSO Γ τ (restrict Γ (cls u) (d n)) fSOu →
      cost Γ τ fSOu ≤ cost Γ τ (restrictProfile Γ (cls u) fSO) ∧
        cost Γ τ (restrictProfile Γ (cls u) fSO) ≤ jointTotalCost Γ τ (cls u) fSO :=
    fun n u fSO fSOu h1 h2 =>
      ⟨h2.2 _ (restrictProfile_isProfile Γ (cls u) (d n) fSO h1.1),
        cost_restrict_le_joint Γ hΓ τ hτ (cls u) fSO h1.1.1⟩
  -- SO and NE profiles of the full game and of the class subgames
  obtain ⟨X, hX⟩ := cost_pos Γ hΓ τ hτ hnd
  choose fSOn hfSOn using fun n => exists_SO_profile Γ hΓ τ hτ (d n) (hdnn n)
  choose fSOu hfSOu using fun (u : Fin m) (n : ℕ) =>
    exists_SO_profile Γ hΓ τ hτ (restrict Γ (cls u) (d n)) (restrict_nonneg Γ _ _ (hdnn n))
  choose fNEu hfNEu using fun (u : Fin m) (n : ℕ) =>
    exists_NE Γ hΓ τ hτ (restrict Γ (cls u) (d n)) (restrict_nonneg Γ _ _ (hdnn n))
  set S : Fin m → ℕ → ℝ := fun u n => SOCost Γ τ (restrict Γ (cls u) (d n)) with hSdef
  set N : Fin m → ℕ → ℝ := fun u n => NECost Γ τ (restrict Γ (cls u) (d n)) with hNdef
  have hS : ∀ u n, S u n = cost Γ τ (fSOu u n) := fun u n => SOCost_eq Γ τ _ _ (hfSOu u n)
  have hN : ∀ u n, N u n = cost Γ τ (fNEu u n) := fun u n => NECost_eq Γ hΓ τ hτ _ _ (hfNEu u n)
  have hS0 : ∀ u n, 0 ≤ S u n := fun u n => by rw [hS]; exact cost_nonneg Γ hΓ τ hτ (hfSOu u n).1.1
  have hSN : ∀ u n, S u n ≤ N u n := fun u n => by
    rw [hS, hN]; exact (hfSOu u n).2 _ (hfNEu u n).1
  have hSpos : ∀ᶠ n in atTop, ∀ u, 0 < S u n := by
    refine Filter.eventually_all.mpr fun u => ?_
    obtain ⟨k, hk⟩ := hclsne u
    filter_upwards [(hdinf k).eventually_ge_atTop X] with n hn
    rw [hS]
    exact hX _ k (by simp only [restrict, if_pos hk]; exact hn) _ (hfSOu u n).1
  obtain ⟨u0, -⟩ := (hcover ⟨0, hΓ.1⟩).mp (Finset.mem_univ _)
  have hSsum : ∀ᶠ n in atTop, 0 < ∑ u, S u n := by
    filter_upwards [hSpos] with n hn
    exact Finset.sum_pos (fun u _ => hn u) ⟨u0, Finset.mem_univ _⟩
  refine ⟨P1, ?_, ?_, ?_⟩
  · -- (2) the PoA rewritten with the joint total costs of an SO profile
    intro fSO hSO
    congr 1
    funext n
    rw [PoA, SOCost_eq Γ τ _ _ (hSO n), joint_sum_eq_cost Γ τ cls hpart]
  · -- (3) the upper bound by the sum of SO costs of the subgames
    apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [hSsum] with n hpos
    have hle : (∑ u, S u n) ≤ SOCost Γ τ (d n) := by
      rw [SOCost_eq Γ τ _ _ (hfSOn n), ← joint_sum_eq_cost Γ τ cls hpart]
      refine Finset.sum_le_sum fun u _ => ?_
      rw [hS]
      exact (P1 n u _ _ (hfSOn n) (hfSOu u n)).1.trans (P1 n u _ _ (hfSOn n) (hfSOu u n)).2
    exact EReal.coe_le_coe_iff.mpr
      (div_le_div_of_nonneg_left (NECost_nonneg Γ hΓ τ hτ _) hpos hle)
  · -- (4) replacing SO costs of the subgames by their NE costs, via Lemma 6 a)
    have h6a : ∀ u, Tendsto (fun n => N u n / S u n) atTop (𝓝 1) := by
      intro u
      have := (lemma_6_a Γ hΓ τ hτ hnd d hdec m cls g hAD0 fNEu fSOu hfNEu hfSOu u).1
      refine this.congr fun n => ?_
      rw [hN, hS]
    -- the ratio of the sums tends to 1
    have hρ : Tendsto (fun n => (∑ u, N u n) / ∑ u, S u n) atTop (𝓝 1) := by
      have hup : Tendsto (fun n => 1 + ∑ u, (N u n / S u n - 1)) atTop (𝓝 1) := by
        have := tendsto_const_nhds (x := (1:ℝ)) |>.add
          (tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun u _ => (h6a u).sub_const 1)
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [hSsum] with n hpos
        rw [le_div_iff₀ hpos, one_mul]
        exact Finset.sum_le_sum fun u _ => hSN u n
      · filter_upwards [hSsum, hSpos] with n hpos hposu
        rw [div_le_iff₀ hpos]
        have hr : ∀ u, 0 ≤ N u n / S u n - 1 := fun u => by
          rw [sub_nonneg, le_div_iff₀ (hposu u), one_mul]; exact hSN u n
        have e : ∀ u, N u n = S u n + S u n * (N u n / S u n - 1) := fun u => by
          field_simp [(hposu u).ne']; ring
        calc (∑ u, N u n) = ∑ u, (S u n + S u n * (N u n / S u n - 1)) :=
              Finset.sum_congr rfl fun u _ => e u
          _ = (∑ u, S u n) + ∑ u, S u n * (N u n / S u n - 1) := Finset.sum_add_distrib
          _ ≤ (∑ u, S u n) + ∑ u, (∑ v, S v n) * (N u n / S u n - 1) := by
              gcongr with u
              · exact hr u
              · exact Finset.single_le_sum (f := fun v => S v n) (fun v _ => hS0 v n)
                  (Finset.mem_univ u)
          _ = (1 + ∑ u, (N u n / S u n - 1)) * ∑ u, S u n := by
              rw [← Finset.mul_sum]; ring
    have hq : Tendsto (fun n => (∑ u, S u n) / ∑ u, N u n) atTop (𝓝 1) := by
      have := hρ.inv₀ one_ne_zero
      simp only [inv_one] at this
      refine this.congr fun n => ?_
      rw [inv_div]
    set x : ℕ → ℝ := fun n => NECost Γ τ (d n) / ∑ u, S u n with hx
    set q : ℕ → ℝ := fun n => (∑ u, S u n) / ∑ u, N u n with hqdef
    have hx0 : ∀ n, 0 ≤ x n := fun n =>
      div_nonneg (NECost_nonneg Γ hΓ τ hτ _) (Finset.sum_nonneg fun u _ => hS0 u n)
    have hq0 : ∀ n, 0 ≤ q n := fun n =>
      div_nonneg (Finset.sum_nonneg fun u _ => hS0 u n)
        (Finset.sum_nonneg fun u _ => (hS0 u n).trans (hSN u n))
    have hqE : Tendsto (fun n => ((q n : ℝ) : EReal)) atTop (𝓝 1) := by
      have := (EReal.tendsto_coe (f := atTop) (m := q) (a := 1)).mpr hq
      simpa using this
    have hlimsup_q : limsup (fun n => ((q n : ℝ) : EReal)) atTop = 1 := hqE.limsup_eq
    have hliminf_q : liminf (fun n => ((q n : ℝ) : EReal)) atTop = 1 := hqE.liminf_eq
    have hbar : ∀ᶠ n in atTop, ((PoABar Γ τ cls (d n) : ℝ) : EReal) =
        ((x n : ℝ) : EReal) * ((q n : ℝ) : EReal) := by
      filter_upwards [hSsum] with n hpos
      have hNpos : 0 < ∑ u, N u n :=
        hpos.trans_le (Finset.sum_le_sum fun u _ => hSN u n)
      rw [← EReal.coe_mul]
      congr 1
      simp only [PoABar, hx, hqdef]
      change NECost Γ τ (d n) / (∑ u, N u n) = _
      field_simp
    rw [limsup_congr hbar]
    let U : ℕ → EReal := fun n => ((x n : ℝ) : EReal)
    let V : ℕ → EReal := fun n => ((q n : ℝ) : EReal)
    have hU : ∃ᶠ n in atTop, 0 ≤ U n :=
      (Eventually.of_forall fun n => EReal.coe_nonneg.mpr (hx0 n)).frequently
    have hV : 0 ≤ᶠ[atTop] V := Eventually.of_forall fun n => EReal.coe_nonneg.mpr (hq0 n)
    have h1 := EReal.limsup_mul_le hU hV
      (Or.inr (by rw [hlimsup_q]; exact (EReal.coe_ne_top 1 : ((1:ℝ):EReal) ≠ ⊤)))
      (Or.inr (by rw [hlimsup_q]; simp))
    have h2 := EReal.le_limsup_mul hU hV
    rw [hlimsup_q, mul_one] at h1
    rw [hliminf_q, mul_one] at h2
    exact le_antisymm h2 h1
