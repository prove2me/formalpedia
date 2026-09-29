-- Prove2me | solution 1 for ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bb78f0bc-89fa-5da5-9998-f0efe5796ed3

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount
import Theorems.Thm_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj
import Theorems.Thm_ModularCurve_cuspCount_mul_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

namespace CuspCountGammaHKer

section GroupTheory

variable {G : Type*} [Group G]

theorem natCard_orbitRelQuotient_eq_natCard_doubleCoset (Γ K : Subgroup G) :
    Nat.card (MulAction.orbitRel.Quotient K (G ⧸ Γ)) =
      Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := by
  have hf₀ : ∀ a b : G, (QuotientGroup.leftRel Γ) a b →
      DoubleCoset.mk Γ K a⁻¹ = DoubleCoset.mk Γ K b⁻¹ := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    rw [DoubleCoset.eq]
    refine ⟨b⁻¹ * a, ?_, 1, K.one_mem, by group⟩
    have := Γ.inv_mem hab
    simpa using this
  let f₀ : G ⧸ Γ → DoubleCoset.Quotient (Γ : Set G) (K : Set G) :=
    Quotient.lift (fun g : G => DoubleCoset.mk Γ K g⁻¹) hf₀
  have hf₀_mk : ∀ g : G, f₀ (QuotientGroup.mk g) = DoubleCoset.mk Γ K g⁻¹ := fun _ => rfl
  have hf₁ : ∀ x y : G ⧸ Γ, (MulAction.orbitRel K (G ⧸ Γ)) x y → f₀ x = f₀ y := by
    intro x y hxy
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
    obtain ⟨k, rfl⟩ := hxy
    induction y using QuotientGroup.induction_on with
    | H g =>
      have h1 : f₀ (k • (QuotientGroup.mk g : G ⧸ Γ)) = DoubleCoset.mk Γ K ((k : G) * g)⁻¹ := rfl
      rw [h1, hf₀_mk, DoubleCoset.eq]
      exact ⟨1, Γ.one_mem, k, k.2, by group⟩
  let f : MulAction.orbitRel.Quotient K (G ⧸ Γ) → DoubleCoset.Quotient (Γ : Set G) (K : Set G) :=
    @Quotient.lift _ _ (MulAction.orbitRel K (G ⧸ Γ)) f₀ hf₁
  have hf_mk : ∀ g : G,
      f (@Quotient.mk _ (MulAction.orbitRel K (G ⧸ Γ)) (QuotientGroup.mk g)) =
        DoubleCoset.mk Γ K g⁻¹ := fun _ => rfl
  apply Nat.card_eq_of_bijective f
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [hf_mk, hf_mk, DoubleCoset.eq] at hxy
    obtain ⟨h, hh, k, hk, hb⟩ := hxy
    apply Quotient.sound
    change (MulAction.orbitRel K (G ⧸ Γ)) _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨⟨k, hk⟩, ?_⟩
    have h2 : (⟨k, hk⟩ : K) • (QuotientGroup.mk b : G ⧸ Γ) = QuotientGroup.mk (k * b) := rfl
    rw [h2, QuotientGroup.eq]
    have hb' : b = k⁻¹ * a * h⁻¹ := by
      have := congrArg (fun z => z⁻¹) hb
      simpa [mul_assoc] using this
    rw [hb']
    have : (k * (k⁻¹ * a * h⁻¹))⁻¹ * a = h := by group
    rw [this]
    exact hh
  · intro z
    induction z using Quotient.inductionOn with
    | h g =>
    refine ⟨@Quotient.mk _ (MulAction.orbitRel K (G ⧸ Γ)) (QuotientGroup.mk g⁻¹), ?_⟩
    rw [hf_mk, inv_inv]

theorem natCard_doubleCoset_ker_eq_index_map {Q : Type*} [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (S : Subgroup G) :
    Nat.card (DoubleCoset.Quotient (π.ker : Set G) (S : Set G)) = (S.map π).index := by
  have hf₀ : ∀ a b : G, (DoubleCoset.setoid (π.ker : Set G) (S : Set G)) a b →
      (QuotientGroup.mk (π a) : Q ⧸ S.map π) = QuotientGroup.mk (π b) := by
    intro a b hab
    obtain ⟨h, hh, s, hs, rfl⟩ := DoubleCoset.rel_iff.mp hab
    rw [QuotientGroup.eq, map_mul, map_mul, (MonoidHom.mem_ker).mp hh, one_mul, inv_mul_cancel_left]
    exact Subgroup.mem_map_of_mem π hs
  let f : DoubleCoset.Quotient (π.ker : Set G) (S : Set G) → Q ⧸ S.map π :=
    @Quotient.lift _ _ (DoubleCoset.setoid (π.ker : Set G) (S : Set G))
      (fun g => (QuotientGroup.mk (π g) : Q ⧸ S.map π)) hf₀
  have hf_mk : ∀ g : G, f (DoubleCoset.mk π.ker S g) = QuotientGroup.mk (π g) := fun _ => rfl
  rw [Subgroup.index]
  apply Nat.card_eq_of_bijective f
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
    change f (DoubleCoset.mk π.ker S a) = f (DoubleCoset.mk π.ker S b) at hxy
    rw [hf_mk, hf_mk, QuotientGroup.eq, Subgroup.mem_map] at hxy
    obtain ⟨s, hs, hs'⟩ := hxy
    change DoubleCoset.mk π.ker S a = DoubleCoset.mk π.ker S b
    rw [DoubleCoset.eq]
    refine ⟨b * s⁻¹ * a⁻¹, ?_, s, hs, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hs']
    group
  · intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
    obtain ⟨g, rfl⟩ := hπ y
    exact ⟨DoubleCoset.mk π.ker S g, hf_mk g⟩

theorem natCard_eq_mul_of_forall_natCard_fibre_eq {α β : Type*} [Finite β] (f : α → β) (m : ℕ)
    (hm : m ≠ 0) (h : ∀ b, Nat.card {a // f a = b} = m) : Nat.card α = m * Nat.card β := by
  classical
  haveI := Fintype.ofFinite β
  haveI : ∀ b, Finite {a // f a = b} := fun b =>
    Nat.finite_of_card_ne_zero (by rw [h b]; exact hm)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  ring

end GroupTheory

section PMUnipotent

def pmUnipotent : Subgroup SL(2, ℤ) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
    (k : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (k : Matrix (Fin 2) (Fin 2) ℤ) 1 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h := Matrix.two_mul_expl (a : Matrix (Fin 2) (Fin 2) ℤ) (b : Matrix (Fin 2) (Fin 2) ℤ)
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [h.1, h.2.2.1, h.2.2.2, ha.1, hb.1, ha.2, hb.2]
    constructor <;> ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', neg_eq_zero]
    exact ⟨ha.1, ha.2.symm⟩

theorem mem_pmUnipotent_iff (k : SL(2, ℤ)) :
    k ∈ pmUnipotent ↔ (k : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
      (k : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (k : Matrix (Fin 2) (Fin 2) ℤ) 1 1 :=
  Iff.rfl

theorem T_mem_pmUnipotent : ModularGroup.T ∈ pmUnipotent := by
  rw [mem_pmUnipotent_iff, ModularGroup.coe_T]
  simp

theorem neg_one_mem_pmUnipotent : (-1 : SL(2, ℤ)) ∈ pmUnipotent := by
  rw [mem_pmUnipotent_iff, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem sup_le_pmUnipotent :
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) ≤ pmUnipotent :=
  sup_le (Subgroup.zpowers_le.mpr T_mem_pmUnipotent) (Subgroup.zpowers_le.mpr neg_one_mem_pmUnipotent)

theorem diag_eq_one_or_of_mem_pmUnipotent {k : SL(2, ℤ)} (hk : k ∈ pmUnipotent) :
    (k : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 ∨ (k : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := by
  have hdet := k.2
  rw [Matrix.det_fin_two, hk.1, hk.2, mul_zero, sub_zero] at hdet
  exact Int.eq_one_or_neg_one_of_mul_eq_one hdet

theorem eq_T_zpow_or_of_mem_pmUnipotent {k : SL(2, ℤ)} (hk : k ∈ pmUnipotent) :
    ∃ x : ℤ, k = ModularGroup.T ^ x ∨ k = -ModularGroup.T ^ x := by
  rcases diag_eq_one_or_of_mem_pmUnipotent hk with h | h
  · refine ⟨(k : Matrix (Fin 2) (Fin 2) ℤ) 0 1, Or.inl ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j
    · simpa [hk.2] using h
    · simp
    · simpa using hk.1
    · simpa using h
  · refine ⟨-(k : Matrix (Fin 2) (Fin 2) ℤ) 0 1, Or.inr ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j
    · simpa [hk.2] using h
    · simp
    · simpa using hk.1
    · simpa using h

end PMUnipotent

section Level

variable (N q : ℕ)

local notation "KK" => (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ))

theorem neg_mem_Gamma0 {a : SL(2, ℤ)} (ha : a ∈ Gamma0 N) : -a ∈ Gamma0 N := by
  rw [Gamma0_mem] at *
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, ha, neg_zero]

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N :=
  neg_mem_Gamma0 N (Subgroup.one_mem _)

theorem natCard_doubleCoset_gamma0_zpowers_T_eq :
    Nat.card (DoubleCoset.Quotient (Gamma0 N : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) =
      Nat.card (DoubleCoset.Quotient (Gamma0 N : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ))) := by
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl _) ?_
  intro x y
  rw [Equiv.refl_apply, Equiv.refl_apply, DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, Subgroup.mem_sup_left hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨n, hn⟩ := eq_T_zpow_or_of_mem_pmUnipotent (sup_le_pmUnipotent hb)
    rcases hn with rfl | rfl
    · exact ⟨a, ha, ModularGroup.T ^ n, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n, rfl⟩
    · refine ⟨-a, neg_mem_Gamma0 N ha, ModularGroup.T ^ n,
        Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n, ?_⟩
      simp [mul_neg, neg_mul]

theorem natCard_doubleCoset_gamma0_eq_cuspCount [NeZero N] :
    Nat.card (DoubleCoset.Quotient (Gamma0 N : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ))) = cuspCount N := by
  rw [← natCard_doubleCoset_gamma0_zpowers_T_eq, ← natCard_orbitRelQuotient_eq_natCard_doubleCoset]
  exact ModularCurve.natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount N

variable {N q}

noncomputable def piHom (hqN : q ∣ N) : ↥(Gamma0 N) →* (ZMod q)ˣ :=
  (ZMod.unitsMap hqN).comp (CohCarrier.gamma0Units N)

theorem coe_piHom_apply (hqN : q ∣ N) (γ : Gamma0 N) :
    ((piHom hqN γ : (ZMod q)ˣ) : ZMod q) = (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod q) := by
  rw [piHom, MonoidHom.comp_apply, ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units]
  change (ZMod.castHom hqN (ZMod q)) ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_intCast hqN]

theorem ker_piHom (hqN : q ∣ N) :
    (piHom hqN).ker = (CohCarrier.GammaH N (ZMod.unitsMap hqN).ker).subgroupOf (Gamma0 N) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, CohCarrier.mem_GammaH_iff]
  constructor
  · intro h
    refine ⟨γ.2, ?_⟩
    rw [MonoidHom.mem_ker, Subtype.coe_eta]
    exact h
  · rintro ⟨hγ, h⟩
    rw [MonoidHom.mem_ker, Subtype.coe_eta] at h
    exact h

theorem gamma0Units_surjective [NeZero N] : Function.Surjective (CohCarrier.gamma0Units N) := by
  intro u
  set d : ℤ := (((u : ZMod N)).val : ℤ) with hd
  set a : ℤ := ((((u⁻¹ : (ZMod N)ˣ) : ZMod N)).val : ℤ) with ha
  have had : ((a * d - 1 : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_sub, Int.cast_mul, ha, hd, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, Int.cast_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp had
  have hdet : Matrix.det !![a, k; (N : ℤ), d] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hk
  have hmem : (⟨!![a, k; (N : ℤ), d], hdet⟩ : SL(2, ℤ)) ∈ Gamma0 N := by
    apply Gamma0_mem.mpr
    simp
  refine ⟨⟨_, hmem⟩, ?_⟩
  ext
  rw [CohCarrier.val_gamma0Units]
  change (((!![a, k; (N : ℤ), d] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = _
  simp [hd]

theorem piHom_surjective [NeZero N] (hqN : q ∣ N) : Function.Surjective (piHom hqN) :=
  (ZMod.unitsMap_surjective hqN).comp gamma0Units_surjective

theorem conj_entries (β k : SL(2, ℤ)) (hk : k ∈ pmUnipotent) :
    ((β * k * β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        -((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
          (k : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) ∧
      ((β * k * β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
        (k : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
          ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (k : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
  have hdet := β.2
  rw [Matrix.det_fin_two] at hdet
  have h1 := Matrix.two_mul_expl ((β * k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    ((β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  have h2 := Matrix.two_mul_expl (β : Matrix (Fin 2) (Fin 2) ℤ) (k : Matrix (Fin 2) (Fin 2) ℤ)
  have hi : ((β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ∧
      ((β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
      ((β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      ((β⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl β]
    simp
  rw [Matrix.SpecialLinearGroup.coe_mul, h1.2.2.1, h1.2.2.2, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2,
    Matrix.SpecialLinearGroup.coe_mul, h2.2.2.1, h2.2.2.2, hk.1, hk.2]
  constructor
  · ring
  · linear_combination (k : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * hdet

theorem map_piHom_stabilizer_eq [Fact q.Prime] (hqN : q ∣ N) (β : SL(2, ℤ)) :
    ((Gamma0 N ⊓ (KK).map (MulAut.conj β).toMonoidHom).subgroupOf (Gamma0 N)).map (piHom hqN) =
      Subgroup.zpowers (-1) := by
  have hq : (q : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hqN
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  apply le_antisymm
  · intro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨γ, hγ, rfl⟩ := hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_map] at hγ
    obtain ⟨hγ0, k, hk, hkγ⟩ := hγ
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkγ
    have hkP := sup_le_pmUnipotent hk
    have hent := conj_entries β k hkP
    rw [hkγ] at hent

    have h10 : ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ0
    rw [hent.1, Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
    have hqacx : (q : ℤ) ∣ (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
        ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (k : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
      rcases hqp.dvd_or_dvd (hq.trans h10) with h | h
      · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h _) _
      · exact Dvd.dvd.mul_left h _
    have hval : ((piHom hqN γ : (ZMod q)ˣ) : ZMod q) = ((k : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod q) := by
      rw [coe_piHom_apply, hent.2, Int.cast_add, (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hqacx, add_zero]
    rcases diag_eq_one_or_of_mem_pmUnipotent hkP with h1 | h1
    · have : piHom hqN γ = 1 := Units.ext (by rw [hval, h1, Int.cast_one, Units.val_one])
      rw [this]
      exact Subgroup.one_mem _
    · have : piHom hqN γ = -1 := Units.ext (by rw [hval, h1, Int.cast_neg, Int.cast_one, Units.val_neg,
        Units.val_one])
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, Subgroup.mem_map]
    have hmem : (-1 : SL(2, ℤ)) ∈ Gamma0 N ⊓ (KK).map (MulAut.conj β).toMonoidHom := by
      rw [Subgroup.mem_inf, Subgroup.mem_map]
      refine ⟨neg_one_mem_Gamma0 N, -1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simp
    refine ⟨⟨-1, neg_one_mem_Gamma0 N⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    apply Units.ext
    rw [coe_piHom_apply, Units.val_neg, Units.val_one]
    change ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q) = -1
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    simp

theorem two_mul_index_zpowers_neg_one [Fact q.Prime] (hq3 : 3 ≤ q) :
    2 * (Subgroup.zpowers (-1 : (ZMod q)ˣ)).index = q - 1 := by
  haveI : Fact (2 < q) := ⟨by omega⟩
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hcard : Nat.card (Subgroup.zpowers (-1 : (ZMod q)ˣ)) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime (by simp) ?_
    intro h
    exact ZMod.neg_one_ne_one (n := q) (by simpa using congrArg Units.val h)
  have h := Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod q)ˣ))
  rw [hcard, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out] at h
  exact h

theorem two_mul_natCard_fibre_eq [NeZero N] [Fact q.Prime] (hq3 : 3 ≤ q) (hqN : q ∣ N) (β : SL(2, ℤ)) :
    2 * Nat.card {x : DoubleCoset.Quotient (CohCarrier.GammaH N (ZMod.unitsMap hqN).ker : Set SL(2, ℤ))
        ((KK) : Set SL(2, ℤ)) //
        ∃ g : SL(2, ℤ), DoubleCoset.mk (CohCarrier.GammaH N (ZMod.unitsMap hqN).ker) (KK) g = x ∧
          DoubleCoset.mk (Gamma0 N) (KK) g = DoubleCoset.mk (Gamma0 N) (KK) β} = q - 1 := by
  rw [DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj (KK)
      (CohCarrier.GammaH_le_Gamma0 _) β, ← ker_piHom hqN,
    natCard_doubleCoset_ker_eq_index_map (piHom hqN) (piHom_surjective hqN),
    map_piHom_stabilizer_eq hqN β, two_mul_index_zpowers_neg_one hq3]

theorem cuspCount_pos (hN : N ≠ 0) : 0 < cuspCount N := by
  rw [cuspCount]
  have h1 : Nat.totient (Nat.gcd 1 (N / 1)) = 1 := by simp
  calc 0 < 1 := Nat.one_pos
    _ = Nat.totient (Nat.gcd 1 (N / 1)) := h1.symm
    _ ≤ ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d)) :=
        Finset.single_le_sum (f := fun d => Nat.totient (Nat.gcd d (N / d))) (fun _ _ => Nat.zero_le _)
          (Nat.one_mem_divisors.mpr hN)

theorem two_mul_natCard_doubleCoset_gammaH_ker_eq [NeZero N] [Fact q.Prime] (hq3 : 3 ≤ q) (hqN : q ∣ N) :
    2 * Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH N (ZMod.unitsMap hqN).ker : Set SL(2, ℤ))
        ((KK) : Set SL(2, ℤ))) = (q - 1) * cuspCount N := by
  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH N (ZMod.unitsMap hqN).ker with hΓ
  have hΓle : Γ ≤ Gamma0 N := CohCarrier.GammaH_le_Gamma0 _

  have hp : ∀ a b : SL(2, ℤ), (DoubleCoset.setoid (Γ : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ))) a b →
      (DoubleCoset.setoid (Gamma0 N : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ))) a b := by
    intro a b hab
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := hab
    exact ⟨x, hΓle hx, y, hy, rfl⟩
  let p : DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ)) →
      DoubleCoset.Quotient (Gamma0 N : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ)) :=
    Quotient.map' id hp
  have hp_mk : ∀ g, p (DoubleCoset.mk Γ (KK) g) = DoubleCoset.mk (Gamma0 N) (KK) g := fun _ => rfl

  have hbase := natCard_doubleCoset_gamma0_eq_cuspCount N
  haveI : Finite (DoubleCoset.Quotient (Gamma0 N : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ))) :=
    Nat.finite_of_card_ne_zero (by rw [hbase]; exact (cuspCount_pos (NeZero.ne N)).ne')

  set m : ℕ := (Subgroup.zpowers (-1 : (ZMod q)ˣ)).index with hm
  have h2m : 2 * m = q - 1 := two_mul_index_zpowers_neg_one hq3
  have hfib : ∀ b, Nat.card {x // p x = b} = m := by
    intro b
    induction b using Quotient.inductionOn with
    | h β =>
    have hβ : (Quotient.mk _ β : DoubleCoset.Quotient (Gamma0 N : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ))) =
        DoubleCoset.mk (Gamma0 N) (KK) β := rfl
    rw [hβ]
    have hfβ := two_mul_natCard_fibre_eq (N := N) hq3 hqN β
    rw [← hΓ] at hfβ
    have heq : Nat.card {x // p x = DoubleCoset.mk (Gamma0 N) (KK) β} =
        Nat.card {x : DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) ((KK) : Set SL(2, ℤ)) //
          ∃ g : SL(2, ℤ), DoubleCoset.mk Γ (KK) g = x ∧
            DoubleCoset.mk (Gamma0 N) (KK) g = DoubleCoset.mk (Gamma0 N) (KK) β} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · intro hx
        induction x using Quotient.inductionOn with
        | h g => exact ⟨g, rfl, by rw [← hp_mk]; exact hx⟩
      · rintro ⟨g, rfl, hg⟩
        rw [hp_mk]
        exact hg
    rw [heq]
    omega
  have hm0 : m ≠ 0 := by omega
  rw [natCard_eq_mul_of_forall_natCard_fibre_eq p m hm0 hfib, ← mul_assoc, h2m, hbase]

end Level

theorem cuspCount_prime_sq (q : ℕ) (hq : q.Prime) : cuspCount (q ^ 2) = q + 1 := by
  rw [cuspCount, Nat.divisors_prime_pow hq 2, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one]
  have h1 : q ^ 2 / q = q := by rw [sq, Nat.mul_div_cancel _ hq.pos]
  have h2 : q ^ 2 / q ^ 2 = 1 := Nat.div_self (pow_pos hq.pos 2)
  rw [Nat.div_one, h1, h2, Nat.gcd_one_left, Nat.gcd_self, Nat.gcd_one_right, Nat.totient_one,
    Nat.totient_prime hq]
  have := hq.one_lt
  omega

end CuspCountGammaHKer

open CuspCountGammaHKer in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    2 * Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) =
      (q ^ 2 - 1) * cuspCount M' := by
  have hqp : q.Prime := Fact.out
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ hqp.ne_zero) (NeZero.ne M')⟩
  have hH : levelH q M' = (ZMod.unitsMap (dvd_sq_mul q M')).ker := rfl
  rw [hH, two_mul_natCard_doubleCoset_gammaH_ker_eq hq (dvd_sq_mul q M'),
    ModularCurve.cuspCount_mul_of_coprime (pow_ne_zero _ hqp.ne_zero) (NeZero.ne M')
      (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqM')),
    cuspCount_prime_sq q hqp, ← mul_assoc]
  congr 1
  rw [mul_comm, ← one_pow 2, Nat.sq_sub_sq, one_pow]

end S_ModularCurve_FullLevel_two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq (solution)
