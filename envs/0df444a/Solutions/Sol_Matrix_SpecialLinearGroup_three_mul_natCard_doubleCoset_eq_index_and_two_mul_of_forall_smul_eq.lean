-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b25fbcc7-8d96-5fb3-8c8a-49dafa5c5397

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq

set_option autoImplicit false

open scoped MatrixGroups

namespace DCEll

section General

variable {G : Type*} [Group G] (Γ K : Subgroup G) (K₀ : Subgroup K)

noncomputable def dcMap :
    DoubleCoset.Quotient (Γ : Set G) (K : Set G) × _root_.Quotient (QuotientGroup.rightRel K₀) →
      _root_.Quotient (QuotientGroup.rightRel Γ) :=
  fun qc => Quotient.mk'' (qc.1.out * ((qc.2.out : K) : G))

theorem dcMap_apply (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G))
    (c : _root_.Quotient (QuotientGroup.rightRel K₀)) :
    dcMap Γ K K₀ (q, c) = Quotient.mk'' (q.out * ((c.out : K) : G)) := rfl

variable (hK₀ : ∀ g : G, ∀ k : K, g * (k : G) * g⁻¹ ∈ Γ ↔ k ∈ K₀)
include hK₀

theorem mk_mul_eq_of_rel (g : G) {k k' : K} (h : k' * k⁻¹ ∈ K₀) :
    (Quotient.mk'' (g * (k' : G)) : _root_.Quotient (QuotientGroup.rightRel Γ)) =
      Quotient.mk'' (g * (k : G)) := by
  refine Quotient.sound' (QuotientGroup.rightRel_apply.mpr ?_)
  have : g * (k : G) * (g * (k' : G))⁻¹ = g * ((k * k'⁻¹ : K) : G) * g⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [this, hK₀]
  simpa using K₀.inv_mem h

theorem dcMap_surjective : Function.Surjective (dcMap Γ K K₀) := by
  intro x
  refine Quotient.inductionOn' x (fun g => ?_)
  obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  set q := DoubleCoset.mk Γ K g
  let kk : K := ⟨k⁻¹, K.inv_mem hk⟩
  refine ⟨(q, Quotient.mk'' kk), ?_⟩
  rw [dcMap_apply]

  set c : _root_.Quotient (QuotientGroup.rightRel K₀) := Quotient.mk'' kk
  have hc : (c.out : K) * kk⁻¹ ∈ K₀ := by
    have : @Setoid.r _ (QuotientGroup.rightRel K₀) kk c.out :=
      Quotient.exact' (by rw [Quotient.out_eq'])
    exact QuotientGroup.rightRel_apply.mp this
  rw [mk_mul_eq_of_rel Γ K K₀ hK₀ q.out hc]
  refine Quotient.sound' (QuotientGroup.rightRel_apply.mpr ?_)
  rw [he]
  have : g * (h * g * k * ((kk : K) : G))⁻¹ = h⁻¹ := by
    show g * (h * g * k * k⁻¹)⁻¹ = h⁻¹
    group
  rw [this]
  exact Γ.inv_mem hh

theorem dcMap_injective : Function.Injective (dcMap Γ K K₀) := by
  rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ h
  rw [dcMap_apply, dcMap_apply] at h
  set k₁ : K := c₁.out
  set k₂ : K := c₂.out
  have h' : (q₂.out * (k₂ : G)) * (q₁.out * (k₁ : G))⁻¹ ∈ Γ :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact' h)
  have hq : DoubleCoset.mk Γ K q₁.out = DoubleCoset.mk Γ K q₂.out :=
    (DoubleCoset.eq Γ K _ _).2 ⟨(q₂.out * (k₂ : G)) * (q₁.out * (k₁ : G))⁻¹, h', (k₁ : G) * (k₂ : G)⁻¹,
      K.mul_mem k₁.2 (K.inv_mem k₂.2), by group⟩
  rw [DoubleCoset.out_eq', DoubleCoset.out_eq'] at hq
  subst hq
  have h'' : q₁.out * (((k₂ * k₁⁻¹ : K)) : G) * q₁.out⁻¹ ∈ Γ := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using h'
  rw [hK₀] at h''
  have hc : c₁ = c₂ := by
    rw [← Quotient.out_eq' c₁, ← Quotient.out_eq' c₂]
    exact Quotient.sound' (QuotientGroup.rightRel_apply.mpr h'')
  rw [hc]

theorem index_mul_card_eq_natCard_doubleCoset_mul :
    Γ.index * Nat.card K₀ = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) * Nat.card K := by
  have h1 : Γ.index = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) * K₀.index :=
    calc Γ.index = Nat.card (G ⧸ Γ) := rfl
      _ = Nat.card (_root_.Quotient (QuotientGroup.rightRel Γ)) :=
          Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ).symm
      _ = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G) ×
            _root_.Quotient (QuotientGroup.rightRel K₀)) :=
          Nat.card_congr (Equiv.ofBijective (dcMap Γ K K₀)
            ⟨dcMap_injective Γ K K₀ hK₀, dcMap_surjective Γ K K₀ hK₀⟩).symm
      _ = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) *
            Nat.card (_root_.Quotient (QuotientGroup.rightRel K₀)) := Nat.card_prod _ _
      _ = _ := by
          congr 1
          exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel K₀)
  rw [h1, mul_assoc, Subgroup.index_mul_card]

end General

theorem mem_zpowers_neg_one {z : SL(2, ℤ)} (hz : z ∈ Subgroup.zpowers (-1 : SL(2, ℤ))) : z = 1 ∨ z = -1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left; rw [← two_mul, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow]
  · right; rw [zpow_add, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow, one_mul, zpow_one]

scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases mem_zpowers_neg_one hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg, mul_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem natCard_doubleCoset_sup_eq (Γ K : Subgroup SL(2, ℤ)) (hK : (-1 : SL(2, ℤ)) ∈ K) :
    Nat.card (DoubleCoset.Quotient ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))
        (K : Set SL(2, ℤ))) =
      Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) (K : Set SL(2, ℤ))) := by
  refine Nat.card_congr (Quotient.congrRight fun x y => ?_)
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩

    obtain ⟨a', ha', z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨a', ha', (-1 : SL(2, ℤ)) ^ n * b, K.mul_mem (K.zpow_mem hK n) hb, ?_⟩
    have hc : Commute ((-1 : SL(2, ℤ)) ^ n) x := (Commute.neg_one_left x).zpow_left n
    calc a' * (-1) ^ n * x * b = a' * ((-1) ^ n * x) * b := by group
      _ = a' * (x * (-1) ^ n) * b := by rw [hc.eq]
      _ = a' * x * ((-1) ^ n * b) := by group
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, Subgroup.mem_sup_left ha, b, hb, rfl⟩

open Matrix.SpecialLinearGroup ModularGroup

theorem exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ r : ℕ, r < m ∧ x ^ r = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h0 : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k (by exact_mod_cast hm.ne')
  have h1 : k % (m : ℤ) < m := Int.emod_lt_of_pos k (by exact_mod_cast hm)
  refine ⟨(k % (m : ℤ)).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod' k hx, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem S_sq : ModularGroup.S ^ 2 = (-1 : SL(2, ℤ)) :=
  Subtype.ext (by rw [coe_pow, pow_two, S_mul_S_eq, coe_neg, Matrix.SpecialLinearGroup.coe_one])

theorem S_pow_four : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, S_sq, neg_one_sq]

theorem coe_ST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![0, -1; 1, 1] := by
  rw [coe_mul, coe_S, coe_T, Matrix.mul_fin_two]
  norm_num

theorem coe_ST_sq : (((ModularGroup.S * ModularGroup.T) ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-1, -1; 1, 0] := by
  rw [coe_pow, coe_ST, pow_two, Matrix.mul_fin_two]
  norm_num

theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  rw [pow_succ, coe_mul, coe_ST_sq, coe_ST, coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two,
    Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem ST_pow_six : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, ST_pow_three, neg_one_sq]

theorem natCard_zpowers_S : Nat.card (Subgroup.zpowers ModularGroup.S) = 4 := by
  rw [Nat.card_zpowers]
  refine (orderOf_eq_iff (by norm_num)).2 ⟨S_pow_four, fun m hm hm0 h => ?_⟩
  interval_cases m
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_one, coe_S, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [S_sq, coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_succ, S_sq, neg_one_mul, coe_neg, coe_S, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'

theorem natCard_zpowers_ST : Nat.card (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) = 6 := by
  rw [Nat.card_zpowers]
  refine (orderOf_eq_iff (by norm_num)).2 ⟨ST_pow_six, fun m hm hm0 h => ?_⟩
  interval_cases m
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_one, coe_ST, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
    rw [coe_ST_sq, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [ST_pow_three, coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    rw [pow_succ, ST_pow_three, neg_one_mul, coe_neg, coe_ST, Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'
  · have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
    rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, ST_pow_three, neg_one_mul, coe_neg, coe_ST_sq,
      Matrix.SpecialLinearGroup.coe_one] at h'
    norm_num at h'

theorem neg_one_mem_zpowers_S : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers ModularGroup.S := by
  rw [← S_sq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

theorem neg_one_mem_zpowers_ST : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers (ModularGroup.S * ModularGroup.T) := by
  rw [← ST_pow_three]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3

variable (Γ : Subgroup SL(2, ℤ))
  (hfree : ∀ γ : SL(2, ℤ), (γ ∈ Γ ∨ -γ ∈ Γ) → ∀ τ : UpperHalfPlane, γ • τ = τ → γ = 1 ∨ γ = -1)
include hfree

theorem conj_mem_sup_iff (x : SL(2, ℤ)) (τ₀ : UpperHalfPlane) (hx : x • τ₀ = τ₀)
    (hneg : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers x) (g : SL(2, ℤ)) (k : Subgroup.zpowers x) :
    g * (k : SL(2, ℤ)) * g⁻¹ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔
      k ∈ (Subgroup.zpowers (-1 : SL(2, ℤ))).subgroupOf (Subgroup.zpowers x) := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp h
    obtain ⟨r, hr, rfl⟩ := exists_pow_eq_of_mem_zpowers (m := 2) (by norm_num) neg_one_sq hz
    set γ := g * (k : SL(2, ℤ)) * g⁻¹ with hγ
    have hγΓ : γ ∈ Γ ∨ -γ ∈ Γ := by
      interval_cases r
      · left; rw [pow_zero, mul_one] at hyz; rw [← hyz]; exact hy
      · right
        rw [pow_one] at hyz
        have : -γ = y := by rw [← hyz, mul_neg_one, neg_neg]
        rwa [this]

    have hk : (k : SL(2, ℤ)) • τ₀ = τ₀ := by
      have hmem : (k : SL(2, ℤ)) ∈ MulAction.stabilizer SL(2, ℤ) τ₀ :=
        (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hx)) k.2
      exact MulAction.mem_stabilizer_iff.mp hmem
    have hfix : γ • (g • τ₀) = g • τ₀ := by
      rw [hγ, mul_smul, mul_smul, inv_smul_smul, hk]
    rcases hfree γ hγΓ (g • τ₀) hfix with h1 | h1
    · have : (k : SL(2, ℤ)) = 1 := by
        have := congrArg (fun t => g⁻¹ * t * g) h1
        simpa [hγ, mul_assoc] using this
      rw [this]; exact Subgroup.one_mem _
    · have : (k : SL(2, ℤ)) = -1 := by
        have := congrArg (fun t => g⁻¹ * t * g) h1
        simpa [hγ, mul_assoc] using this
      rw [this]; exact Subgroup.mem_zpowers _
  · intro h
    obtain ⟨r, hr, hrk⟩ := exists_pow_eq_of_mem_zpowers (m := 2) (by norm_num) neg_one_sq h
    interval_cases r
    · rw [pow_zero] at hrk; rw [← hrk, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    · rw [pow_one] at hrk
      rw [← hrk, mul_neg_one, neg_mul, mul_inv_cancel]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem natCard_subgroupOf_neg_one (x : SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers x) :
    Nat.card ((Subgroup.zpowers (-1 : SL(2, ℤ))).subgroupOf (Subgroup.zpowers x)) = 2 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hneg)).toEquiv, Nat.card_zpowers]
  refine (orderOf_eq_iff (by norm_num)).2 ⟨neg_one_sq, fun m hm hm0 h => ?_⟩
  interval_cases m
  have h' := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  rw [pow_one, coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
  norm_num at h'

theorem two_mul_index_eq (x : SL(2, ℤ)) (τ₀ : UpperHalfPlane) (hx : x • τ₀ = τ₀)
    (hneg : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers x) :
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index * 2 =
      Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) (Subgroup.zpowers x : Set SL(2, ℤ))) *
        Nat.card (Subgroup.zpowers x) := by
  have h := index_mul_card_eq_natCard_doubleCoset_mul _ _ _ (conj_mem_sup_iff Γ hfree x τ₀ hx hneg)
  rw [natCard_subgroupOf_neg_one Γ hfree x hneg, natCard_doubleCoset_sup_eq Γ _ hneg] at h
  exact h

end DCEll
p2m_reactivate "P2MW.S_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq.DCEll"

open DCEll in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hfree : ∀ γ : SL(2, ℤ), (γ ∈ Γ ∨ -γ ∈ Γ) → ∀ τ : UpperHalfPlane, γ • τ = τ → γ = 1 ∨ γ = -1) :
    3 * Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) =
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
          (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) =
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  have hSTρ : (ModularGroup.S * ModularGroup.T) • UpperHalfPlane.ρ = UpperHalfPlane.ρ :=
    ModularGroup.stabilizer_ρ.mpr (by simp)
  have hSI : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I :=
    ModularGroup.stabilizer_I.mpr (by simp)
  have hST := two_mul_index_eq Γ hfree _ _ hSTρ neg_one_mem_zpowers_ST
  have hS := two_mul_index_eq Γ hfree _ _ hSI neg_one_mem_zpowers_S
  rw [natCard_zpowers_ST] at hST
  rw [natCard_zpowers_S] at hS
  constructor <;> omega

end S_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq (solution)
