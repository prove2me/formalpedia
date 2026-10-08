-- Prove2me | solution 1 for MathieuM23.m23_isSimpleGroup
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T10:38:41.063094+00:00
-- url     : https://prove2.me/submissions/dcfce92c-4ea3-4894-9134-e2f75b2c8117

import Definitions.Def_MathieuM23_Group

open MathieuM23

set_option maxRecDepth 100000

namespace MathieuM23Sol

lemma g₁_mem : g₁ ∈ M23 := Subgroup.subset_closure (by simp)
lemma g₂_mem : g₂ ∈ M23 := Subgroup.subset_closure (by simp)

lemma g₂_pow : g₂ ^ 23 = 1 := by decide +kernel
lemma g₂_ne : g₂ ≠ 1 := by decide +kernel
lemma g₃_pow : ((g₁ * g₂)⁻¹) ^ 23 = 1 := by decide +kernel
lemma g₃_ne : (g₁ * g₂)⁻¹ ≠ 1 := by decide +kernel
lemma g₂_reach : ∀ y : Fin 23, ∃ i : Fin 23, (g₂ ^ (i : ℕ)) 0 = y := by decide +kernel

lemma prime23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩

lemma g₂_order : orderOf g₂ = 23 := by
  have := prime23
  exact orderOf_eq_prime g₂_pow g₂_ne

lemma g₃_order : orderOf ((g₁ * g₂)⁻¹) = 23 := by
  have := prime23
  exact orderOf_eq_prime g₃_pow g₃_ne

/-- `M23` is transitive on `Fin 23`. -/
lemma trans : ∀ x y : Fin 23, ∃ g : M23, (g : Equiv.Perm (Fin 23)) x = y := by
  intro x y
  obtain ⟨i, hi⟩ := g₂_reach x
  obtain ⟨j, hj⟩ := g₂_reach y
  have h2 : g₂ ∈ M23 := g₂_mem
  refine ⟨⟨g₂ ^ (j : ℕ) * (g₂ ^ (i : ℕ))⁻¹, ?_⟩, ?_⟩
  · exact M23.mul_mem (M23.pow_mem h2 _) (M23.inv_mem (M23.pow_mem h2 _))
  · simp only [Equiv.Perm.mul_apply]
    rw [← hi]
    simp [hj]

/-- A nontrivial normal subgroup of `M23` has order divisible by 23. -/
lemma dvd_card (N : Subgroup M23) [N.Normal] (hN : N ≠ ⊥) : 23 ∣ Nat.card N := by
  by_contra hnd
  apply hN
  have hblock : MulAction.IsBlock M23 (MulAction.orbit N (0 : Fin 23)) :=
    MulAction.IsBlock.orbit_of_normal 0
  have : MulAction.IsPretransitive M23 (Fin 23) := ⟨trans⟩
  have hdvd : Set.ncard (MulAction.orbit N (0 : Fin 23)) ∣ 23 := by
    have := hblock.ncard_dvd_card ⟨0, MulAction.mem_orbit_self 0⟩
    simpa using this
  have := prime23
  rcases (Nat.dvd_prime prime23.out).1 hdvd with h1 | h23
  · -- orbit of 0 is {0}
    have hfix0 : ∀ n : N, ((n : M23) : Equiv.Perm (Fin 23)) 0 = 0 := by
      intro n
      rw [Set.ncard_eq_one] at h1
      obtain ⟨a, ha⟩ := h1
      have h0 : (0 : Fin 23) ∈ MulAction.orbit N (0 : Fin 23) := MulAction.mem_orbit_self 0
      have hn : n • (0 : Fin 23) ∈ MulAction.orbit N (0 : Fin 23) := MulAction.mem_orbit _ _
      rw [ha, Set.mem_singleton_iff] at h0 hn
      exact hn.trans h0.symm
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    refine Subtype.ext (Equiv.ext fun x => ?_)
    obtain ⟨g, hg⟩ := trans 0 x
    have hnorm : g⁻¹ * (n : M23) * g ∈ N := by
      have := (inferInstance : N.Normal).conj_mem n hn g⁻¹
      simpa using this
    have h3 : ((g⁻¹ * (n : M23) * g : M23) : Equiv.Perm (Fin 23)) 0 = 0 := hfix0 ⟨_, hnorm⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply] at h3
    have h4 := congrArg (g : Equiv.Perm (Fin 23)) h3
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h4
    rw [hg] at h4
    simpa using h4
  · have := Subgroup.index_mul_card (MulAction.stabilizer N (0 : Fin 23))
    rw [MulAction.index_stabilizer, h23] at this
    exact (hnd (Dvd.intro _ this)).elim

lemma card_G_dvd : Nat.card M23 ∣ Nat.factorial 23 := by
  have := Subgroup.card_subgroup_dvd_card M23
  rw [Nat.card_perm] at this
  have h23 : Nat.card (Fin 23) = 23 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h23] at this
  exact this

lemma not_dvd_fact : ¬ (23 ^ 2 ∣ Nat.factorial 23) := by
  rw [show Nat.factorial 23 = 25852016738884976640000 by decide +kernel]
  norm_num

/-- Every subgroup of order 23 of `M23` is a Sylow 23-subgroup. -/
lemma sylow_of_card (P : Subgroup M23) (hP : Nat.card P = 23) :
    ∃ Q : Sylow 23 M23, (Q : Subgroup M23) = P := by
  have := prime23
  have hpg : IsPGroup 23 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  refine ⟨Q, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hdvdQ : Nat.card Q ∣ Nat.factorial 23 :=
    (Subgroup.card_subgroup_dvd_card (Q : Subgroup M23)).trans card_G_dvd
  have h23Q : 23 ∣ Nat.card (Q : Subgroup M23) := by
    have := Subgroup.card_dvd_of_le hQ; rwa [hP] at this
  have hn1 : n = 1 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp at hn; rw [hn] at h23Q; norm_num at h23Q
      · rfl
    · exfalso
      apply not_dvd_fact
      refine dvd_trans (pow_dvd_pow 23 h) ?_
      rw [← hn]; exact hdvdQ
  subst hn1
  exact (Subgroup.eq_of_le_of_card_ge hQ (by rw [hn, hP]; simp)).symm

/-- An element of order 23 of `M23` generates a Sylow 23-subgroup. -/
lemma sylow_zpowers (g : M23) (hg : orderOf g = 23) :
    ∃ Q : Sylow 23 M23, (Q : Subgroup M23) = Subgroup.zpowers g :=
  sylow_of_card _ (by rw [Nat.card_zpowers, hg])

/-- If `N` is normal and contains one element of order 23, it contains all of them. -/
lemma mem_of_order (N : Subgroup M23) [N.Normal] (g h : M23) (hg : orderOf g = 23)
    (hh : orderOf h = 23) (hgN : g ∈ N) : h ∈ N := by
  have := prime23
  obtain ⟨Q1, hQ1⟩ := sylow_zpowers g hg
  obtain ⟨Q2, hQ2⟩ := sylow_zpowers h hh
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M23 Q1 Q2
  have hmem : h ∈ (Q2 : Subgroup M23) := by
    rw [hQ2]; exact Subgroup.mem_zpowers h
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  rw [hQ1] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hkN : g ^ k ∈ N := N.zpow_mem hgN k
  have : c * g ^ k * c⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ hkN c
  have e : c * g ^ k * c⁻¹ = h := by
    rw [hk]
    simp [MulAut.smul_def]
    group
  rwa [e] at this

theorem main : IsSimpleGroup M23 := by
  have := prime23
  have : Nontrivial M23 := ⟨⟨⟨g₁, g₁_mem⟩, 1, by
    intro h
    have : g₁ = 1 := congrArg Subtype.val h
    revert this; decide +kernel⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxN, hx⟩ : ∃ x : M23, x ∈ N ∧ orderOf x = 23 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 23 (dvd_card N hbot)
    exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩
  let a : M23 := ⟨g₂, g₂_mem⟩
  let b : M23 := ⟨(g₁ * g₂)⁻¹, M23.inv_mem (M23.mul_mem g₁_mem g₂_mem)⟩
  have ha : orderOf a = 23 := (Subgroup.orderOf_coe a).symm.trans g₂_order
  have hb : orderOf b = 23 := (Subgroup.orderOf_coe b).symm.trans g₃_order
  have haN : a ∈ N := mem_of_order N x a hx ha hxN
  have hbN : b ∈ N := mem_of_order N x b hx hb hxN
  have h1 : (⟨g₁, g₁_mem⟩ : M23) = (a * b)⁻¹ := by
    apply Subtype.ext
    simp only [a, b]
    decide +kernel
  have hg1N : (⟨g₁, g₁_mem⟩ : M23) ∈ N := by rw [h1]; exact N.inv_mem (N.mul_mem haN hbN)
  rw [eq_top_iff]
  intro y hy0
  clear hy0
  obtain ⟨y, hy⟩ := y
  change y ∈ Subgroup.closure {g₁, g₂} at hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact hg1N
    · rw [Set.mem_singleton_iff] at hz; subst hz; exact haN
  | one => exact N.one_mem
  | mul u v hu hv ih1 ih2 => exact N.mul_mem ih1 ih2
  | inv u hu ih => exact N.inv_mem ih

end MathieuM23Sol

theorem solution : IsSimpleGroup M23 := MathieuM23Sol.main

