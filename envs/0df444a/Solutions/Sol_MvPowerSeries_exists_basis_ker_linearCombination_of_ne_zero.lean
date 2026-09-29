-- Prove2me | solution 1 for MvPowerSeries.exists_basis_ker_linearCombination_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fae10f5e-1173-58bc-a9cf-cf3999899326

import Mathlib
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2mRelFree

open MvPowerSeries

variable {κ : Type} [Field κ]

local notation "𝔸" => MvPowerSeries (Fin 2) κ

scoped instance instNoeth : IsNoetherianRing 𝔸 := MvPowerSeries.isNoetherianRing_fin κ 2

scoped instance instDomain : IsDomain 𝔸 := NoZeroDivisors.to_isDomain _

theorem X_ne_zero' (s : Fin 2) : (X s : 𝔸) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single s 1)) h
  rw [coeff_X, coeff_zero, if_pos rfl] at this
  exact one_ne_zero this

theorem X0_dvd_of_X1_mul_eq (a b : 𝔸) (h : X 1 * a = X 0 * b) : (X 0 : 𝔸) ∣ a := by
  classical
  rw [X_dvd_iff]
  intro e he
  have h0 : (X 0 : 𝔸) ∣ X 1 * a := ⟨b, h⟩
  have h1 := (X_dvd_iff.mp h0) (e + Finsupp.single 1 1) (by
    rw [Finsupp.add_apply, Finsupp.single_apply, he]
    decide)
  rw [X_def, coeff_monomial_mul, if_pos (by
    intro t
    rw [Finsupp.add_apply]
    exact le_add_self), one_mul, add_tsub_cancel_right] at h1
  exact h1

theorem exists_eq_X0_mul_add_X1_mul (g : 𝔸) (hg : constantCoeff g = 0) :
    ∃ p q : 𝔸, g = X 0 * p + X 1 * q := by
  classical

  let r : 𝔸 := fun e => if e 0 = 0 then coeff e g else 0
  have hr : ∀ e, coeff e r = if e 0 = 0 then coeff e g else 0 := fun e => rfl
  have h0 : (X 0 : 𝔸) ∣ (g - r) := by
    rw [X_dvd_iff]
    intro e he
    rw [map_sub, hr, if_pos he, sub_self]
  have h1 : (X 1 : 𝔸) ∣ r := by
    rw [X_dvd_iff]
    intro e he
    rw [hr]
    by_cases h : e 0 = 0
    · rw [if_pos h]
      have : e = 0 := by
        ext t
        fin_cases t
        · exact h
        · exact he
      rw [this]
      exact hg
    · rw [if_neg h]
  obtain ⟨p, hp⟩ := h0
  obtain ⟨q, hq⟩ := h1
  exact ⟨p, q, by rw [← hp, ← hq, sub_add_cancel]⟩

theorem constantCoeff_eq_zero_of_not_isUnit (g : 𝔸) (hg : ¬ IsUnit g) : constantCoeff g = 0 := by
  rw [isUnit_iff_constantCoeff] at hg
  by_contra h
  exact hg (Ne.isUnit h)

theorem X_mem_maximalIdeal (s : Fin 2) : (X s : 𝔸) ∈ IsLocalRing.maximalIdeal 𝔸 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

theorem span_X_le_jacobson : (Ideal.span {(X 0 : 𝔸), X 1} : Ideal 𝔸) ≤ Ideal.jacobson ⊥ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le]
  rintro x hx
  rcases hx with rfl | rfl
  · exact X_mem_maximalIdeal 0
  · exact X_mem_maximalIdeal 1

variable {m : ℕ}

def Saturated (K : Submodule 𝔸 (Fin m → 𝔸)) : Prop :=
  ∀ (a : 𝔸) (v : Fin m → 𝔸), a ≠ 0 → a • v ∈ K → v ∈ K

theorem saturated_ker (f : Fin m → 𝔸) : Saturated (LinearMap.ker (Fintype.linearCombination 𝔸 f)) := by
  intro a v ha hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [map_smul, smul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left ha

theorem exists_eq_X0_smul (K : Submodule 𝔸 (Fin m → 𝔸)) (hK : Saturated K) (w w' : Fin m → 𝔸)
    (hw : w ∈ K) (h : (X 1 : 𝔸) • w = (X 0 : 𝔸) • w') : ∃ v ∈ K, w = (X 0 : 𝔸) • v := by
  have hdvd : ∀ i, (X 0 : 𝔸) ∣ w i := fun i => X0_dvd_of_X1_mul_eq (w i) (w' i) (by
    have := congrFun h i
    simpa only [Pi.smul_apply, smul_eq_mul] using this)
  choose v hv using hdvd
  have hw' : w = (X 0 : 𝔸) • v := funext fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact hv i
  refine ⟨v, hK (X 0) v (X_ne_zero' 0) (hw' ▸ hw), hw'⟩

theorem ker_eq_bot_of_forall_not_isUnit {n : ℕ} (K : Submodule 𝔸 (Fin m → 𝔸)) (hK : Saturated K)
    (k : Fin n → (Fin m → 𝔸)) (hspan : Submodule.span 𝔸 (Set.range k) = K)
    (hmin : ∀ c : Fin n → 𝔸, Fintype.linearCombination 𝔸 k c = 0 → ∀ i, ¬ IsUnit (c i)) :
    LinearMap.ker (Fintype.linearCombination 𝔸 k) = ⊥ := by
  classical
  set φ := Fintype.linearCombination 𝔸 k with hφ
  have hrange : LinearMap.range φ = K := by rw [hφ, Fintype.range_linearCombination]; exact hspan
  have hNfg : (LinearMap.ker φ).FG := IsNoetherian.noetherian _
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(X 0 : 𝔸), X 1}) _ hNfg ?_ span_X_le_jacobson
  intro c hc
  have hc0 : φ c = 0 := hc

  have hcomp : ∀ i, ∃ p q : 𝔸, c i = X 0 * p + X 1 * q := fun i =>
    exists_eq_X0_mul_add_X1_mul (c i) (constantCoeff_eq_zero_of_not_isUnit (c i) (hmin c hc0 i))
  choose a b hab using hcomp
  have hc_eq : c = (X 0 : 𝔸) • a + (X 1 : 𝔸) • b := funext fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hab i
  have hφa : φ a ∈ K := hrange ▸ LinearMap.mem_range_self φ a
  have hφb : φ b ∈ K := hrange ▸ LinearMap.mem_range_self φ b

  have hrel : (X 1 : 𝔸) • φ b = (X 0 : 𝔸) • (-φ a) := by
    have h1 : (X 0 : 𝔸) • φ a + (X 1 : 𝔸) • φ b = 0 := by
      rw [← map_smul, ← map_smul, ← map_add, ← hc_eq]
      exact hc0
    rw [smul_neg, eq_neg_iff_add_eq_zero, add_comm]
    exact h1
  obtain ⟨v, hvK, hv⟩ := exists_eq_X0_smul K hK (φ b) (-φ a) hφb hrel
  have hvr : v ∈ LinearMap.range φ := by rw [hrange]; exact hvK
  obtain ⟨d, hd⟩ := hvr

  have hb' : b - (X 0 : 𝔸) • d ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, hd, ← hv, sub_self]
  have hc_eq' : c = (X 0 : 𝔸) • (a + (X 1 : 𝔸) • d) + (X 1 : 𝔸) • (b - (X 0 : 𝔸) • d) := by
    rw [hc_eq, smul_add, smul_sub, smul_smul, smul_smul, mul_comm (X 0 : 𝔸) (X 1)]
    abel
  have ha' : a + (X 1 : 𝔸) • d ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    have h1 : (X 0 : 𝔸) • φ (a + (X 1 : 𝔸) • d) + (X 1 : 𝔸) • φ (b - (X 0 : 𝔸) • d) = 0 := by
      rw [← map_smul, ← map_smul, ← map_add, ← hc_eq']
      exact hc0
    rw [LinearMap.mem_ker] at hb'
    rw [hb', smul_zero, add_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_left (X_ne_zero' 0)
  rw [hc_eq']
  exact Submodule.add_mem _
    (Submodule.smul_mem_smul (Ideal.subset_span (by simp)) ha')
    (Submodule.smul_mem_smul (Ideal.subset_span (by simp)) hb')

theorem exists_basis_of_forall_not_isUnit {n : ℕ} (K : Submodule 𝔸 (Fin m → 𝔸)) (hK : Saturated K)
    (k : Fin n → (Fin m → 𝔸)) (hspan : Submodule.span 𝔸 (Set.range k) = K)
    (hmin : ∀ c : Fin n → 𝔸, Fintype.linearCombination 𝔸 k c = 0 → ∀ i, ¬ IsUnit (c i)) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) 𝔸 K) := by
  classical
  set φ := Fintype.linearCombination 𝔸 k with hφ
  have hrange : LinearMap.range φ = K := by rw [hφ, Fintype.range_linearCombination]; exact hspan
  have hker : LinearMap.ker φ = ⊥ := ker_eq_bot_of_forall_not_isUnit K hK k hspan hmin
  have hmem : ∀ c, φ c ∈ K := fun c => hrange ▸ LinearMap.mem_range_self φ c
  let φK : (Fin n → 𝔸) →ₗ[𝔸] K := LinearMap.codRestrict K φ hmem
  have hinj : Function.Injective φK := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict]
    exact hker
  have hsurj : Function.Surjective φK := by
    intro x
    have hx : (x : Fin m → 𝔸) ∈ LinearMap.range φ := by rw [hrange]; exact x.2
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, Subtype.ext hc⟩
  exact ⟨n, ⟨(Pi.basisFun 𝔸 (Fin n)).map (LinearEquiv.ofBijective φK ⟨hinj, hsurj⟩)⟩⟩

theorem exists_basis_of_saturated (K : Submodule 𝔸 (Fin m → 𝔸)) (hK : Saturated K) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) 𝔸 K) := by
  classical
  have hfg : K.FG := IsNoetherian.noetherian K
  obtain ⟨n, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg

  induction n with
  | zero => exact exists_basis_of_forall_not_isUnit K hK k hk (fun c _ i => (IsEmpty.false i).elim)
  | succ n ih =>
    by_cases h : ∃ c : Fin (n + 1) → 𝔸, Fintype.linearCombination 𝔸 k c = 0 ∧ ∃ i, IsUnit (c i)
    ·
      obtain ⟨c, hc, i, hu⟩ := h
      obtain ⟨uu, huu⟩ := hu
      apply ih (k ∘ i.succAbove)
      apply le_antisymm
      · rw [← hk]
        exact Submodule.span_mono (Set.range_comp_subset_range _ _)
      · rw [← hk]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        by_cases hji : j = i
        · subst hji

          have hsum : c j • k j + ∑ l, c (j.succAbove l) • k (j.succAbove l) = 0 := by
            rw [Fintype.linearCombination_apply, Fin.sum_univ_succAbove _ j] at hc
            exact hc
          have hkj : k j = ((uu⁻¹ : 𝔸ˣ) : 𝔸) • (-(∑ l, c (j.succAbove l) • k (j.succAbove l))) := by
            rw [← eq_neg_iff_add_eq_zero.mpr hsum, smul_smul, ← huu, Units.inv_mul, one_smul]
          rw [hkj]
          refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun l _ => ?_))
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
        · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hji
          exact Submodule.subset_span ⟨l, by simp only [Function.comp_apply, hl]⟩
    · push Not at h
      exact exists_basis_of_forall_not_isUnit K hK k hk (fun c hc i hu => h c hc i hu)

theorem card_add_one_eq {m : ℕ} (f : Fin m → 𝔸) (hf : f ≠ 0) {r : ℕ}
    (e : Module.Basis (Fin r) 𝔸 (LinearMap.ker (Fintype.linearCombination 𝔸 f))) : r + 1 = m := by
  classical
  set L := Fintype.linearCombination 𝔸 f with hL
  have h := LinearMap.rank_range_add_rank_ker L
  rw [rank_fin_fun, rank_eq_card_basis e, Fintype.card_fin] at h

  have hne : ∃ x : LinearMap.range L, x ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf (funext hall)
    refine ⟨⟨f i, ⟨Pi.single i 1, ?_⟩⟩, fun h0 => hi (congrArg Subtype.val h0)⟩
    rw [hL, Fintype.linearCombination_apply, Fintype.sum_eq_single i (fun j hj => by
      rw [Pi.single_apply, if_neg hj, zero_smul]), Pi.single_apply, if_pos rfl, one_smul]
  have h1 : Module.rank 𝔸 (LinearMap.range L) = 1 := by
    apply le_antisymm
    · calc Module.rank 𝔸 (LinearMap.range L) ≤ Module.rank 𝔸 𝔸 := Submodule.rank_le _
        _ = 1 := Module.rank_self 𝔸
    · exact Cardinal.one_le_iff_pos.mpr (rank_pos_iff_exists_ne_zero.mpr hne)
  rw [h1] at h
  have h' : ((1 + r : ℕ) : Cardinal) = (m : Cardinal) := by push_cast; exact h
  have := (Nat.cast_inj (R := Cardinal)).mp h'
  omega

end P2mRelFree
p2m_reactivate "P2MW.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero.P2mRelFree"

open P2mRelFree in
theorem solution
    {κ : Type} [Field κ] {m : ℕ} (f : Fin m → MvPowerSeries (Fin 2) κ) (hf : f ≠ 0) :
    ∃ (r : ℕ) (e : Module.Basis (Fin r) (MvPowerSeries (Fin 2) κ)
        (LinearMap.ker (Fintype.linearCombination (MvPowerSeries (Fin 2) κ) f))), r + 1 = m := by
  obtain ⟨r, ⟨e⟩⟩ := exists_basis_of_saturated _ (saturated_ker f)
  exact ⟨r, e, card_add_one_eq f hf e⟩

end S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero
end P2MW
export P2MW.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero (solution)
