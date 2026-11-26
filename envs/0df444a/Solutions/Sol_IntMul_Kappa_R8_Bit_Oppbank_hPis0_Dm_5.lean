-- Prove2me | solution 5 for IntMul.Kappa.R8.Bit.Oppbank.hPis0_Dm
-- status  : ACCEPTED   (disprove)
-- author  : @scuba8684
-- created : 2026-11-26T07:53:17.214648+00:00
-- url     : https://prove2.me/submissions/224ce64a-9d7a-4231-aee1-3d836dfed63c

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private theorem nested_of_idempotent_difference {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℚ) (hP : P * P = P) (hQ : Q * Q = Q)
    (hD : (Q - P) * (Q - P) = Q - P) : Q * P = P := by
  have hsum : Q * P + P * Q = P + P := by
    rw [sub_mul, mul_sub, mul_sub, hP, hQ] at hD
    ext i j
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℚ => A i j) hD
    simp only [Matrix.sub_apply, Matrix.add_apply] at h ⊢
    linarith only [h]
  have hl := congrArg (fun A : Matrix (Fin n) (Fin n) ℚ => P * A) hsum
  change P * (Q * P + P * Q) = P * (P + P) at hl
  rw [mul_add, mul_add, ← mul_assoc P P Q, hP] at hl
  have hr := congrArg (fun A : Matrix (Fin n) (Fin n) ℚ => A * P) hsum
  change (Q * P + P * Q) * P = (P + P) * P at hr
  simp only [add_mul, mul_assoc, hP] at hr
  ext i j
  let entry := fun A : Matrix (Fin n) (Fin n) ℚ => A i j
  have h₁ := congrArg entry hsum
  have h₂ := congrArg entry hl
  have h₃ := congrArg entry hr
  simp only [entry, Matrix.add_apply] at h₁ h₂ h₃
  linarith only [h₁, h₂, h₃]


private theorem single_support {i j : ℕ} (h : (2 ^ i).testBit j = true) : i = j :=
  of_decide_eq_true (Nat.testBit_two_pow ▸ h)

private theorem singleton_span (i : ℕ) :
    spanS (2 ^ i) = Submodule.span ℚ {tvQ i} := by
  unfold spanS
  congr 1
  ext v
  constructor
  · rintro ⟨j, h, rfl⟩
    obtain rfl := single_support h
    rfl
  · rintro rfl
    exact ⟨i, Nat.testBit_two_pow_self, rfl⟩

private theorem singleton_centre {i : ℕ} (hi : i < 1771)
    (hc : (triL i).testBit 0 = true) (hw : ∑ p : Fin 23, tvQ i p = 3) :
    HasCentre (2 ^ i) := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  obtain rfl := single_support hj
  exact ⟨hi, hc, hw⟩

private theorem mask_zero : densSupG 0 = 2 ^ 0 := by decide +kernel
private theorem mask_one : densSupG 1 = 2 ^ 1 := by decide +kernel

private theorem centre_zero : HasCentre (densSupG 0) := by
  rw [mask_zero]
  exact singleton_centre (by decide) (by decide +kernel) (by decide +kernel)

private theorem centre_one : HasCentre (densSupG 1) := by
  rw [mask_one]
  exact singleton_centre (by decide) (by decide +kernel) (by decide +kernel)

private theorem projected_mem {s : ℕ} (h : HasCentre s) (v : V23) :
    Pnd s *ᵥ v ∈ spanS s := by
  rw [Pnd_eq_prj h, prjM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  exact Submodule.projection_apply_mem _ _

private theorem projected_fixed {s : ℕ} (h : HasCentre s) {v : V23} (hv : v ∈ spanS s) :
    Pnd s *ᵥ v = v := by
  rw [Pnd_eq_prj h, prjM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  exact Submodule.projection_apply_left (p := spanS s) (q := Bf.orthogonal (spanS s))
    (compl_spanS h) ⟨v, hv⟩

theorem solution : ¬ (∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A) := by
  intro all_idempotent
  have ho : 1773 < codeBound := by decide +kernel
  have hc : 1774 < codeBound := by decide +kernel
  have nested : nestOK 1773 1774 = true := by decide +kernel
  have orient : dimCF 1773 ≤ dimCF 1774 := by decide +kernel
  have po : Pc 1773 = Pnd (densSupG 0) := Pc_of_ND 0 ho
  have pc : Pc 1774 = Pnd (densSupG 1) := Pc_of_ND 1 hc
  have in_idx : (1773, 1774) ∈ idxD := (MoveFacts3.mem_idxD _).2 ⟨⟨ho, hc⟩, nested⟩
  have diff := all_idempotent (Dm 1773 1774) (Finset.mem_image.mpr ⟨(1773, 1774), in_idx, rfl⟩)
  rw [Dm, if_pos orient, po, pc] at diff
  have product := nested_of_idempotent_difference _ _ (PndIdem.Pnd_idem centre_zero)
    (PndIdem.Pnd_idem centre_one) diff
  have member : tvQ 0 ∈ spanS (densSupG 0) := by
    rw [mask_zero, singleton_span]
    exact Submodule.subset_span rfl
  have fixed := projected_fixed centre_zero member
  have fixed_by_second : Pnd (densSupG 1) *ᵥ tvQ 0 = tvQ 0 := by
    calc
      _ = Pnd (densSupG 1) *ᵥ (Pnd (densSupG 0) *ᵥ tvQ 0) := by rw [fixed]
      _ = (Pnd (densSupG 1) * Pnd (densSupG 0)) *ᵥ tvQ 0 := by rw [Matrix.mulVec_mulVec]
      _ = tvQ 0 := by rw [product, fixed]
  have member_second := projected_mem centre_one (tvQ 0)
  rw [fixed_by_second, mask_one, singleton_span] at member_second
  obtain ⟨r, he⟩ := Submodule.mem_span_singleton.mp member_second
  have test := congrFun he (2 : Fin 23)
  have val₀ : tvQ 0 (2 : Fin 23) = 1 := by decide +kernel
  have val₁ : tvQ 1 (2 : Fin 23) = 0 := by decide +kernel
  simp only [Pi.smul_apply, smul_eq_mul, val₀, val₁, mul_zero] at test
  exact zero_ne_one test
