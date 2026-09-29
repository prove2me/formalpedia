-- Prove2me | solution 1 for MvFormalGroup.coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0ec559f1-ee30-57ff-8e7f-62422c38ead2

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open MvPowerSeries

universe u

namespace HWIterate

variable (p : ℕ) [hp : Fact p.Prime]

private theorem hp0 : p ≠ 0 := hp.out.ne_zero

private theorem hpk (k : ℕ) : p ^ k ≠ 0 := pow_ne_zero k (hp0 p)

omit hp in

private theorem expand_congr {σ : Type*} (a b : ℕ) (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : MvPowerSeries σ (ZMod p)) : expand a ha f = expand b hb f := by
  subst h; rfl

section PrimeField

variable {σ : Type*}

private theorem expand_eq_pow (k : ℕ) (f : MvPowerSeries σ (ZMod p)) :
    expand (p ^ k) (hpk p k) f = f ^ p ^ k := by
  have h := map_iterateFrobenius_expand p (hp0 p) f k
  have hid : ∀ g : MvPowerSeries σ (ZMod p), map (iterateFrobenius (ZMod p) p k) g = g := by
    intro g
    ext m
    rw [coeff_map, iterateFrobenius_def, ZMod.pow_card_pow]
  rwa [hid] at h

private theorem subst_expand {τ : Type*} (k : ℕ) {f : σ → MvPowerSeries τ (ZMod p)} (hf : HasSubst f)
    (φ : MvPowerSeries σ (ZMod p)) :
    subst f (expand (p ^ k) (hpk p k) φ) = expand (p ^ k) (hpk p k) (subst f φ) := by
  have h1 : expand (p ^ k) (hpk p k) φ = subst (fun s : σ => (X s : MvPowerSeries σ (ZMod p)) ^ p ^ k) φ := by
    rw [expand, coe_substAlgHom]
  rw [expand_subst _ _ hf, h1, subst_comp_subst_apply (HasSubst.X_pow (hpk p k)) hf]
  congr 1
  funext s
  rw [subst_pow hf, subst_X hf, expand_eq_pow]

private theorem expand_injective (k : ℕ) : Function.Injective (expand (σ := σ) (R := ZMod p) (p ^ k) (hpk p k)) := by
  intro f g h
  ext m
  rw [← coeff_expand_smul (p ^ k) (hpk p k) f m, ← coeff_expand_smul (p ^ k) (hpk p k) g m, h]

end PrimeField

section Law

variable {d : ℕ} (F : MvFormalGroup d (ZMod p)) [F.IsComm]

private def IsEndo (θ : Fin d → MvPowerSeries (Fin d) (ZMod p)) : Prop :=
  ∀ i, subst F.toPowerSeries (θ i) =
    subst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p))) (θ j))
      (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p))) (θ j)))
      (F.toPowerSeries i)

private theorem isEndo_nthSeries (n : ℕ) : IsEndo p F (F.nthSeries n) ∧ ∀ i, (F.nthSeries n i).constantCoeff = 0 := by
  rw [← MvFormalGroup.End.toPowerSeries_natCast]
  exact ⟨fun i => (n : MvFormalGroup.End F).subst_eq i, fun i => (n : MvFormalGroup.End F).constantCoeff_eq_zero i⟩

omit [F.IsComm] in

private theorem isEndo_of_isEndo_expand (k : ℕ) {θ : Fin d → MvPowerSeries (Fin d) (ZMod p)}
    (hθ0 : ∀ i, (θ i).constantCoeff = 0)
    (h : IsEndo p F (fun i => expand (p ^ k) (hpk p k) (θ i))) : IsEndo p F θ := by
  intro i
  apply expand_injective p k
  have hF : HasSubst F.toPowerSeries := F.hasSubst_toPowerSeries
  have hl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p))) :=
    HasSubst.X_comp _
  have hr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) (ZMod p))) :=
    HasSubst.X_comp _
  rw [← subst_expand p k hF, h i, expand_subst _ _ (MvFormalGroup.hasSubst_elim
    (fun j => constantCoeff_subst_eq_zero hl (fun l => constantCoeff_X _) (hθ0 j))
    (fun j => constantCoeff_subst_eq_zero hr (fun l => constantCoeff_X _) (hθ0 j)))]
  congr 1
  funext s
  rcases s with j | j
  · simp only [Sum.elim_inl]; rw [subst_expand p k hl]
  · simp only [Sum.elim_inr]; rw [subst_expand p k hr]

private theorem exists_iterate (G : Fin d → MvPowerSeries (Fin d) (ZMod p)) (hG0 : ∀ i, (G i).constantCoeff = 0)
    (hG : ∀ i, F.nthSeries p i = expand (p ^ 1) (hpk p 1) (G i)) (k : ℕ) :
    ∃ Q : Fin d → MvPowerSeries (Fin d) (ZMod p),
      (∀ i, (Q i).constantCoeff = 0) ∧
      (∀ i, F.nthSeries (p ^ k) i = expand (p ^ k) (hpk p k) (Q i)) ∧
      MvFormalGroup.linearPart Q = MvFormalGroup.linearPart G ^ k := by
  induction k with
  | zero =>
    refine ⟨fun i => X i, fun i => constantCoeff_X i, fun i => ?_, ?_⟩
    · rw [expand_congr p (p ^ 0) 1 (pow_zero p) (hpk p 0) one_ne_zero, expand_one_apply, pow_zero]
      change F.nthSeries (0 + 1) i = X i
      rw [MvFormalGroup.nthSeries_succ, MvFormalGroup.nthSeries_zero]
      exact MvFormalGroup.subst_elim_zero_X F i
    · rw [pow_zero, MvFormalGroup.linearPart_X]
  | succ k ih =>
    obtain ⟨Q, hQ0, hQ, hlin⟩ := ih
    have hGs : HasSubst G := hasSubst_of_constantCoeff_zero hG0
    refine ⟨fun i => subst G (Q i), fun i => constantCoeff_subst_eq_zero hGs hG0 (hQ0 i), fun i => ?_, ?_⟩
    ·
      have hmul : F.nthSeries (p ^ (k + 1)) i = subst (F.nthSeries p) (F.nthSeries (p ^ k) i) := by
        rw [← MvFormalGroup.End.toPowerSeries_natCast, ← MvFormalGroup.End.toPowerSeries_natCast,
          ← MvFormalGroup.End.toPowerSeries_natCast, Nat.cast_pow, Nat.cast_pow, pow_succ,
          MvFormalGroup.End.toPowerSeries_mul]
      have hEG : HasSubst (fun j => expand (p ^ 1) (hpk p 1) (G j)) := HasSubst.expand _ _ hGs
      rw [hmul, hQ i, show F.nthSeries p = fun j => expand (p ^ 1) (hpk p 1) (G j) from funext hG,
        subst_expand p k hEG, ← expand_subst _ _ hGs, ← expand_mul]
      exact expand_congr p _ _ (by rw [← pow_add]) _ _ _
    · rw [MvFormalGroup.linearPart_subst hG0, hlin, pow_succ]

end Law

end HWIterate

open HWIterate in
theorem solution
    (p : ℕ) [Fact p.Prime] {d : ℕ} (F : MvFormalGroup d (ZMod p)) [F.IsComm]
    (ν : ℕ)
    (hB : (Matrix.of fun i j : Fin d => (F.nthSeries p i).coeff (Finsupp.single j p)) ^ ν = 0)
    (i : Fin d) (m : Fin d →₀ ℕ) (hm : ∃ j, ¬ p ^ (ν + 1) ∣ m j) :
    (F.nthSeries (p ^ ν) i).coeff m = 0 := by
  classical

  obtain ⟨hEp, hp0c⟩ := isEndo_nthSeries p F p
  have hlinp : MvFormalGroup.linearPart (F.nthSeries p) = 0 := by
    rw [MvFormalGroup.linearPart_nthSeries]
    ext a b
    rw [Matrix.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Matrix.zero_apply]
  have hvan : ∀ (i : Fin d) (m : Fin d →₀ ℕ), (∃ j, ¬ p ∣ m j) → (F.nthSeries p i).coeff m = 0 :=
    fun i m hm => MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP p F F (F.nthSeries p)
      hp0c hlinp hEp i m hm

  let G : Fin d → MvPowerSeries (Fin d) (ZMod p) := fun i m => (F.nthSeries p i).coeff (p • m)
  have hGc : ∀ i m, (G i).coeff m = (F.nthSeries p i).coeff (p • m) := fun i m => rfl
  have hG : ∀ i, F.nthSeries p i = expand (p ^ 1) (hpk p 1) (G i) := by
    intro i
    ext m
    by_cases h : ∀ j, p ∣ m j
    · obtain ⟨a, rfl⟩ : ∃ a : Fin d →₀ ℕ, m = p • a := by
        refine ⟨m.mapRange (· / p) (Nat.zero_div p), ?_⟩
        ext j
        rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, Nat.mul_div_cancel' (h j)]
      rw [expand_congr p (p ^ 1) p (pow_one p) (hpk p 1) (HWIterate.hp0 p), coeff_expand_smul, hGc]
    · push Not at h
      obtain ⟨j, hj⟩ := h
      rw [hvan i m ⟨j, hj⟩, coeff_expand_of_not_dvd _ _ _ (by rwa [pow_one])]
  have hG0 : ∀ i, (G i).constantCoeff = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, hGc, smul_zero, coeff_zero_eq_constantCoeff_apply]; exact hp0c i
  have hlinG : MvFormalGroup.linearPart G = Matrix.of fun i j : Fin d => (F.nthSeries p i).coeff (Finsupp.single j p) := by
    ext i j
    change (G i).coeff (Finsupp.single j 1) = (F.nthSeries p i).coeff (Finsupp.single j p)
    rw [hGc, Finsupp.smul_single, smul_eq_mul, mul_one]

  obtain ⟨Q, hQ0, hQ, hlinQ⟩ := exists_iterate p F G hG0 hG ν
  rw [hlinG, hB] at hlinQ

  obtain ⟨hEν, -⟩ := isEndo_nthSeries p F (p ^ ν)
  have hEQ : IsEndo p F Q := by
    refine isEndo_of_isEndo_expand p F ν hQ0 ?_
    intro i'
    have := hEν i'
    simp only [hQ] at this ⊢
    convert this using 2
  have hvanQ : ∀ (m : Fin d →₀ ℕ), (∃ j, ¬ p ∣ m j) → (Q i).coeff m = 0 :=
    fun m hm => MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP p F F Q hQ0 hlinQ hEQ i m hm

  rw [hQ i]
  by_cases h : ∀ j, p ^ ν ∣ m j
  · obtain ⟨a, rfl⟩ : ∃ a : Fin d →₀ ℕ, m = p ^ ν • a := by
      refine ⟨m.mapRange (· / p ^ ν) (Nat.zero_div _), ?_⟩
      ext j
      rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, Nat.mul_div_cancel' (h j)]
    rw [coeff_expand_smul]
    apply hvanQ
    obtain ⟨j, hj⟩ := hm
    refine ⟨j, fun hpa => hj ?_⟩
    rw [Finsupp.smul_apply, smul_eq_mul, pow_succ]
    exact Nat.mul_dvd_mul_left _ hpa
  · push Not at h
    obtain ⟨j, hj⟩ := h
    exact coeff_expand_of_not_dvd _ _ _ hj

end S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp
end P2MW
export P2MW.S_MvFormalGroup_coeff_nthSeries_pow_eq_zero_of_hasseWitt_pow_eq_zero_zmodp (solution)
