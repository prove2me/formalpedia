-- Prove2me | solution 1 for LocalNewvector.indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0b49a26b-cf3b-5150-8f23-7d34f4ef78a2

import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace SteinbergCell

open LocalNewvector

variable (q : ℕ) [Fact q.Prime]

private def lo (g : GL (Fin 2) ℚ_[q]) : ℚ_[q] := (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0

private def lr (g : GL (Fin 2) ℚ_[q]) : ℚ_[q] := (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1

private theorem lo_mul (g h : GL (Fin 2) ℚ_[q]) :
    lo q (g * h) = lo q g * (h : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0
      + lr q g * (h : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 := by
  simp [lo, lr, Matrix.mul_apply, Fin.sum_univ_two]

private theorem lr_mul (g h : GL (Fin 2) ℚ_[q]) :
    lr q (g * h) = lo q g * (h : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 1
      + lr q g * (h : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 := by
  simp [lo, lr, Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem lo_one : lo q (1 : GL (Fin 2) ℚ_[q]) = 0 := by simp [lo]

@[scoped simp] private theorem lr_one : lr q (1 : GL (Fin 2) ℚ_[q]) = 1 := by simp [lr]

private theorem lo_ne_zero_or_lr_ne_zero (g : GL (Fin 2) ℚ_[q]) : lo q g ≠ 0 ∨ lr q g ≠ 0 := by
  by_contra h
  push Not at h
  have hu := Matrix.isUnits_det_units g
  rw [Matrix.det_fin_two] at hu
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := h.1
  have h2 : (g : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 = 0 := h.2
  rw [h1, h2, mul_zero, mul_zero, sub_zero] at hu
  exact not_isUnit_zero hu

private theorem lr_ne_zero_of_lo_eq_zero {g : GL (Fin 2) ℚ_[q]} (h : lo q g = 0) : lr q g ≠ 0 :=
  (lo_ne_zero_or_lr_ne_zero q g).resolve_left (not_not.mpr h)

private def IsUpper (b : GL (Fin 2) ℚ_[q]) : Prop := lo q b = 0

private theorem isUpper_one : IsUpper q 1 := lo_one q

private theorem isUpper_mul {b b' : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (hb' : IsUpper q b') :
    IsUpper q (b * b') := by
  unfold IsUpper at *
  rw [lo_mul, hb, zero_mul, zero_add]
  change lr q b * lo q b' = 0
  rw [hb', mul_zero]

private theorem upperLeft_ne_zero_of_isUpper {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) :
    (b : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 ≠ 0 := by
  intro h0
  have hu := Matrix.isUnits_det_units b
  rw [Matrix.det_fin_two] at hu
  have h10 : (b : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := hb
  rw [h0, h10, zero_mul, mul_zero, sub_zero] at hu
  exact not_isUnit_zero hu

private theorem isUpper_inv {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) : IsUpper q b⁻¹ := by
  have h := lo_mul q b⁻¹ b
  rw [inv_mul_cancel, lo_one] at h
  have h10 : (b : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := hb
  rw [h10, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (upperLeft_ne_zero_of_isUpper q hb)

private theorem lo_upper_mul {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (g : GL (Fin 2) ℚ_[q]) :
    lo q (b * g) = lr q b * lo q g := by
  rw [lo_mul]
  unfold IsUpper at hb
  rw [hb, zero_mul, zero_add]
  rfl

private theorem lr_upper_mul {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (g : GL (Fin 2) ℚ_[q]) :
    lr q (b * g) = lr q b * lr q g := by
  rw [lr_mul]
  unfold IsUpper at hb
  rw [hb, zero_mul, zero_add]
  rfl

private theorem lr_ne_zero_of_isUpper {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) : lr q b ≠ 0 :=
  lr_ne_zero_of_lo_eq_zero q hb

private theorem exists_borelElem_eq {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) :
    ∃ (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]), b = borelElem q a₁ a₂ x := by
  refine ⟨Units.mk0 _ (upperLeft_ne_zero_of_isUpper q hb), Units.mk0 _ (lr_ne_zero_of_isUpper q hb),
    (b : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 1, ?_⟩
  refine Units.ext ?_
  rw [coe_borelElem]
  ext i j
  have h10 : (b : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := hb
  fin_cases i <;> fin_cases j <;> simp [h10, lr]

private abbrev Kq : Subgroup (GL (Fin 2) ℚ_[q]) := LocalNewvector.padicK1 q 0

private abbrev KM (M : ℕ) : Subgroup (GL (Fin 2) ℚ_[q]) := FLT.SmoothVectors.gl2CongruenceSubgroup q M

private theorem mem_Kq_iff (g : GL (Fin 2) ℚ_[q]) : g ∈ Kq q ↔ g ∈ LocalGL2.integralSubgroup ℤ_[q] ℚ_[q] := by
  rw [show Kq q = LocalGL2.integralSubgroup ℤ_[q] ℚ_[q] from padicK1_zero_eq_integralSubgroup q]

private theorem KM_le_Kq (M : ℕ) : KM q M ≤ Kq q := by
  intro g hg
  have hg0 : g ∈ KM q 0 := FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q (Nat.zero_le M) hg
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff] at hg0
  have hone : ((q : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  rw [hone] at hg0
  rw [mem_Kq_iff, FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem (IsFractionRing.injective ℤ_[q] ℚ_[q]),
    FLT.SpectralSide.range_algebraMap_padicInt q]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h := (FLT.SmoothVectors.norm_sub_one_entry_le_one_iff q).mp (hg0.1 i j)
    exact ⟨⟨_, h⟩, rfl⟩
  · have h := (FLT.SmoothVectors.norm_sub_one_entry_le_one_iff q).mp (hg0.2 i j)
    exact ⟨⟨_, h⟩, rfl⟩

private theorem Kq_le_KM_zero : Kq q ≤ KM q 0 := by
  intro g hg
  rw [mem_Kq_iff] at hg
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem (IsFractionRing.injective ℤ_[q] ℚ_[q]),
    FLT.SpectralSide.range_algebraMap_padicInt q] at hg
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  have hone : ((q : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  rw [hone]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [FLT.SmoothVectors.norm_sub_one_entry_le_one_iff]
    obtain ⟨r, hr⟩ := hg.1 i j
    rw [← hr]
    exact r.2
  · rw [FLT.SmoothVectors.norm_sub_one_entry_le_one_iff]
    obtain ⟨r, hr⟩ := hg.2 i j
    rw [← hr]
    exact r.2

private theorem conj_mem_KM {M : ℕ} {k m : GL (Fin 2) ℚ_[q]} (hk : k ∈ Kq q) (hm : m ∈ KM q M) :
    k * m * k⁻¹ ∈ KM q M :=
  FLT.SmoothVectors.conj_mem_gl2CongruenceSubgroup q (Kq_le_KM_zero q hk) hm

private theorem conj_mem_KM' {M : ℕ} {k m : GL (Fin 2) ℚ_[q]} (hk : k ∈ Kq q) (hm : m ∈ KM q M) :
    k⁻¹ * m * k ∈ KM q M := by
  have h := conj_mem_KM q ((Kq q).inv_mem hk) hm
  rwa [inv_inv] at h

private def Omega (M : ℕ) : Set (GL (Fin 2) ℚ_[q]) :=
  {g | ∃ b m : GL (Fin 2) ℚ_[q], IsUpper q b ∧ m ∈ KM q M ∧ g = b * m}

private theorem mem_Omega_of_isUpper_of_mem {M : ℕ} {b m : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (hm : m ∈ KM q M) :
    b * m ∈ Omega q M :=
  ⟨b, m, hb, hm, rfl⟩

private theorem one_mem_Omega (M : ℕ) : (1 : GL (Fin 2) ℚ_[q]) ∈ Omega q M :=
  ⟨1, 1, isUpper_one q, (KM q M).one_mem, by rw [mul_one]⟩

private theorem upper_mul_mem_Omega_iff {M : ℕ} {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (g : GL (Fin 2) ℚ_[q]) :
    b * g ∈ Omega q M ↔ g ∈ Omega q M := by
  constructor
  · rintro ⟨b', m, hb', hm, h⟩
    refine ⟨b⁻¹ * b', m, isUpper_mul q (isUpper_inv q hb) hb', hm, ?_⟩
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  · rintro ⟨b', m, hb', hm, rfl⟩
    exact ⟨b * b', m, isUpper_mul q hb hb', hm, (mul_assoc _ _ _).symm⟩

private theorem mul_mem_Omega_iff_of_mem_KM {M : ℕ} {m : GL (Fin 2) ℚ_[q]} (hm : m ∈ KM q M) (g : GL (Fin 2) ℚ_[q]) :
    g * m ∈ Omega q M ↔ g ∈ Omega q M := by
  constructor
  · rintro ⟨b', m', hb', hm', h⟩
    refine ⟨b', m' * m⁻¹, hb', (KM q M).mul_mem hm' ((KM q M).inv_mem hm), ?_⟩
    rw [← mul_assoc, ← h, mul_inv_cancel_right]
  · rintro ⟨b', m', hb', hm', rfl⟩
    exact ⟨b', m' * m, hb', (KM q M).mul_mem hm' hm, mul_assoc _ _ _⟩

open Classical in

private def E (M : ℕ) : GL (Fin 2) ℚ_[q] → ℂ := fun g => if g ∈ Omega q M then 1 else 0

private theorem E_of_mem {M : ℕ} {g : GL (Fin 2) ℚ_[q]} (h : g ∈ Omega q M) : E q M g = 1 := by
  simp [E, h]

private theorem E_of_not_mem {M : ℕ} {g : GL (Fin 2) ℚ_[q]} (h : g ∉ Omega q M) : E q M g = 0 := by
  simp [E, h]

private theorem E_mul_KM {M : ℕ} {m : GL (Fin 2) ℚ_[q]} (hm : m ∈ KM q M) (g : GL (Fin 2) ℚ_[q]) :
    E q M (g * m) = E q M g := by
  by_cases h : g ∈ Omega q M
  · rw [E_of_mem q h, E_of_mem q ((mul_mem_Omega_iff_of_mem_KM q hm g).mpr h)]
  · rw [E_of_not_mem q h, E_of_not_mem q (fun h' => h ((mul_mem_Omega_iff_of_mem_KM q hm g).mp h'))]

private theorem qR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos

private theorem one_lt_qR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt

private theorem radius_lt_one' {M : ℕ} (hM : 1 ≤ M) : (q : ℝ) ^ (-(M : ℤ)) < 1 :=
  zpow_lt_one_of_neg₀ (one_lt_qR q) (by omega)

private def lowerU (c : ℚ_[q]) : GL (Fin 2) ℚ_[q] :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

@[scoped simp] private theorem coe_lowerU (c : ℚ_[q]) :
    ((lowerU q c : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![1, 0; c, 1] := rfl

@[scoped simp] private theorem coe_lowerU_inv (c : ℚ_[q]) :
    (((lowerU q c)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![1, 0; -c, 1] := rfl

private theorem lowerU_mem_KM {c : ℚ_[q]} {M : ℕ} (hM : 1 ≤ M) (hc : ‖c‖ ≤ (q : ℝ) ^ (-(M : ℤ))) :
    lowerU q c ∈ KM q M := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hM]
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(M : ℤ)) := by positivity
  generalize (q : ℝ) ^ (-(M : ℤ)) = r at hc hpos ⊢
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, hc, hpos]

private theorem exists_upper_mul_lowerU (g : GL (Fin 2) ℚ_[q]) (h : lr q g ≠ 0) :
    ∃ b : GL (Fin 2) ℚ_[q], IsUpper q b ∧ g = b * lowerU q (lo q g / lr q g) := by
  refine ⟨g * (lowerU q (lo q g / lr q g))⁻¹, ?_, by rw [inv_mul_cancel_right]⟩
  unfold IsUpper
  rw [lo_mul, coe_lowerU_inv]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  unfold lo lr at *
  field_simp
  ring

private theorem norm_lr_eq_one_of_mem_KM {M : ℕ} (hM : 1 ≤ M) {m : GL (Fin 2) ℚ_[q]} (hm : m ∈ KM q M) :
    ‖lr q m‖ = 1 := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hM] at hm
  apply FLT.SmoothVectors.norm_eq_one_of_norm_sub_one_lt_one q
  have h := hm 1 1
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h
  exact lt_of_le_of_lt h (radius_lt_one' q hM)

private theorem norm_lo_le_of_mem_KM {M : ℕ} (hM : 1 ≤ M) {m : GL (Fin 2) ℚ_[q]} (hm : m ∈ KM q M) :
    ‖lo q m‖ ≤ (q : ℝ) ^ (-(M : ℤ)) := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hM] at hm
  have h := hm 1 0
  rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h
  exact h

private theorem mem_Omega_iff_norm {M : ℕ} (hM : 1 ≤ M) (g : GL (Fin 2) ℚ_[q]) :
    g ∈ Omega q M ↔ ‖lo q g‖ ≤ (q : ℝ) ^ (-(M : ℤ)) * ‖lr q g‖ := by
  constructor
  · rintro ⟨b, m, hb, hm, rfl⟩
    rw [lo_upper_mul q hb, lr_upper_mul q hb, norm_mul, norm_mul, norm_lr_eq_one_of_mem_KM q hM hm, mul_one,
      mul_comm ((q : ℝ) ^ (-(M : ℤ)))]
    exact mul_le_mul_of_nonneg_left (norm_lo_le_of_mem_KM q hM hm) (norm_nonneg _)
  · intro h
    have hlr : lr q g ≠ 0 := by
      intro h0
      rw [h0, norm_zero, mul_zero] at h
      have hlo : lo q g = 0 := norm_le_zero_iff.mp h
      exact (lr_ne_zero_of_lo_eq_zero q hlo) h0
    obtain ⟨b, hb, hg⟩ := exists_upper_mul_lowerU q g hlr
    rw [hg]
    refine mem_Omega_of_isUpper_of_mem q hb (lowerU_mem_KM q hM ?_)
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hlr)]
    exact h

private def rt (h : GL (Fin 2) ℚ_[q]) (F : GL (Fin 2) ℚ_[q] → ℂ) : GL (Fin 2) ℚ_[q] → ℂ := fun g => F (g * h)

@[scoped simp] private theorem rt_apply (h : GL (Fin 2) ℚ_[q]) (F : GL (Fin 2) ℚ_[q] → ℂ) (g : GL (Fin 2) ℚ_[q]) :
    rt q h F g = F (g * h) := rfl

private theorem rt_mul (h h' : GL (Fin 2) ℚ_[q]) (F : GL (Fin 2) ℚ_[q] → ℂ) :
    rt q (h * h') F = rt q h (rt q h' F) := by
  funext g
  simp [rt, mul_assoc]

@[scoped simp] private theorem rt_one (F : GL (Fin 2) ℚ_[q] → ℂ) : rt q 1 F = F := by
  funext g
  simp [rt]

private theorem rt_add (h : GL (Fin 2) ℚ_[q]) (F F' : GL (Fin 2) ℚ_[q] → ℂ) :
    rt q h (F + F') = rt q h F + rt q h F' := rfl

private theorem rt_smul (h : GL (Fin 2) ℚ_[q]) (c : ℂ) (F : GL (Fin 2) ℚ_[q] → ℂ) :
    rt q h (c • F) = c • rt q h F := rfl

private theorem rt_sub (h : GL (Fin 2) ℚ_[q]) (F F' : GL (Fin 2) ℚ_[q] → ℂ) :
    rt q h (F - F') = rt q h F - rt q h F' := rfl

private theorem rt_sum {ι : Type*} (s : Finset ι) (h : GL (Fin 2) ℚ_[q]) (F : ι → GL (Fin 2) ℚ_[q] → ℂ) :
    rt q h (∑ i ∈ s, F i) = ∑ i ∈ s, rt q h (F i) := by
  funext g
  simp [rt, Finset.sum_apply]

end SteinbergCell
p2m_reactivate "P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.SteinbergCell"

namespace SteinbergCell

open LocalNewvector

variable (q : ℕ) [Fact q.Prime]

private abbrev upperN (x : ℚ_[q]) : GL (Fin 2) ℚ_[q] := borelElem q 1 1 x

open Classical in

private def diagE (a : ℚ_[q]) : GL (Fin 2) ℚ_[q] :=
  if h : a = 0 then 1 else borelElem q (Units.mk0 a h) 1 0

private theorem diagE_of_ne_zero {a : ℚ_[q]} (h : a ≠ 0) : diagE q a = borelElem q (Units.mk0 a h) 1 0 := by
  unfold diagE
  rw [dif_neg h]

private theorem diagE_zero : diagE q 0 = 1 := by
  unfold diagE
  rw [dif_pos rfl]

private theorem qp_ne_zero : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

private def dq : GL (Fin 2) ℚ_[q] := borelElem q 1 (Units.mk0 (q : ℚ_[q]) (qp_ne_zero q)) 0

private def w0 : GL (Fin 2) ℚ_[q] :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

@[scoped simp] private theorem coe_w0 : ((w0 q : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) = !![0, 1; 1, 0] := rfl

private theorem isUpper_borelElem (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) : IsUpper q (borelElem q a₁ a₂ x) := by
  simp [IsUpper, lo]

private theorem isUpper_upperN (x : ℚ_[q]) : IsUpper q (upperN q x) := isUpper_borelElem q 1 1 x

private theorem isUpper_diagE (a : ℚ_[q]) : IsUpper q (diagE q a) := by
  by_cases h : a = 0
  · rw [h, diagE_zero]
    exact isUpper_one q
  · rw [diagE_of_ne_zero q h]
    exact isUpper_borelElem q _ _ _

private theorem lo_mul_borelElem (g : GL (Fin 2) ℚ_[q]) (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) :
    lo q (g * borelElem q a₁ a₂ x) = lo q g * a₁ := by
  rw [lo_mul, coe_borelElem]
  simp

private theorem lr_mul_borelElem (g : GL (Fin 2) ℚ_[q]) (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) :
    lr q (g * borelElem q a₁ a₂ x) = lo q g * x + lr q g * a₂ := by
  rw [lr_mul, coe_borelElem]
  simp

private theorem lo_mul_upperN (g : GL (Fin 2) ℚ_[q]) (x : ℚ_[q]) : lo q (g * upperN q x) = lo q g := by
  rw [lo_mul_borelElem]; simp

private theorem lr_mul_upperN (g : GL (Fin 2) ℚ_[q]) (x : ℚ_[q]) : lr q (g * upperN q x) = lo q g * x + lr q g := by
  rw [lr_mul_borelElem]; simp

private theorem lo_mul_dq (g : GL (Fin 2) ℚ_[q]) : lo q (g * dq q) = lo q g := by
  rw [dq, lo_mul_borelElem]; simp

private theorem lr_mul_dq (g : GL (Fin 2) ℚ_[q]) : lr q (g * dq q) = lr q g * q := by
  rw [dq, lr_mul_borelElem]; simp

private theorem lo_mul_w0 (g : GL (Fin 2) ℚ_[q]) : lo q (g * w0 q) = lr q g := by
  rw [lo_mul, coe_w0]; simp [lo, lr]

private theorem lr_mul_w0 (g : GL (Fin 2) ℚ_[q]) : lr q (g * w0 q) = lo q g := by
  rw [lr_mul, coe_w0]; simp [lo, lr]

private theorem lo_mul_diagE (g : GL (Fin 2) ℚ_[q]) (a : ℚ_[q]) (h : a ≠ 0) : lo q (g * diagE q a) = lo q g * a := by
  rw [diagE_of_ne_zero q h, lo_mul_borelElem]; simp

private theorem lr_mul_diagE (g : GL (Fin 2) ℚ_[q]) (a : ℚ_[q]) (h : a ≠ 0) : lr q (g * diagE q a) = lr q g := by
  rw [diagE_of_ne_zero q h, lr_mul_borelElem]; simp

private theorem ind_congr {P Q : Prop} {_ : Decidable P} {_ : Decidable Q} (h : P ↔ Q) :
    (if P then (1 : ℂ) else 0) = if Q then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h.mp hP)]
  · rw [if_neg hP, if_neg (fun hQ => hP (h.mpr hQ))]

private def OmegaZ (N : ℤ) : Set (GL (Fin 2) ℚ_[q]) := {g | ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖}

private def Ball (c : ℚ_[q]) (r : ℝ) : Set (GL (Fin 2) ℚ_[q]) := {g | ‖lr q g - c * lo q g‖ ≤ r * ‖lo q g‖}

open Classical in

private def EZ (N : ℤ) : GL (Fin 2) ℚ_[q] → ℂ := fun g => if g ∈ OmegaZ q N then 1 else 0

open Classical in

private def IB (c : ℚ_[q]) (r : ℝ) : GL (Fin 2) ℚ_[q] → ℂ := fun g => if g ∈ Ball q c r then 1 else 0

private theorem mem_OmegaZ_iff (N : ℤ) (g : GL (Fin 2) ℚ_[q]) :
    g ∈ OmegaZ q N ↔ ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖ := Iff.rfl

private theorem mem_Ball_iff (c : ℚ_[q]) (r : ℝ) (g : GL (Fin 2) ℚ_[q]) :
    g ∈ Ball q c r ↔ ‖lr q g - c * lo q g‖ ≤ r * ‖lo q g‖ := Iff.rfl

private theorem Omega_eq_OmegaZ {M : ℕ} (hM : 1 ≤ M) : Omega q M = OmegaZ q (M : ℤ) := by
  ext g
  rw [mem_Omega_iff_norm q hM, mem_OmegaZ_iff]

private theorem E_eq_EZ {M : ℕ} (hM : 1 ≤ M) : E q M = EZ q (M : ℤ) := by
  funext g
  unfold E EZ
  exact ind_congr (by rw [Omega_eq_OmegaZ q hM])

private theorem norm_add_eq_left_of_lt {a b : ℚ_[q]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne (ne_of_gt h), max_eq_left h.le]

private theorem OmegaZ_upper_mul {N : ℤ} {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (g : GL (Fin 2) ℚ_[q]) :
    b * g ∈ OmegaZ q N ↔ g ∈ OmegaZ q N := by
  have hpos : 0 < ‖lr q b‖ := norm_pos_iff.mpr (lr_ne_zero_of_isUpper q hb)
  rw [mem_OmegaZ_iff, mem_OmegaZ_iff, lo_upper_mul q hb, lr_upper_mul q hb, norm_mul, norm_mul,
    mul_left_comm, mul_le_mul_iff_right₀ hpos]

private theorem EZ_upper_mul {N : ℤ} {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) (g : GL (Fin 2) ℚ_[q]) :
    EZ q N (b * g) = EZ q N g :=
  ind_congr (OmegaZ_upper_mul q hb g)

private theorem EZ_apply (N : ℤ) (g : GL (Fin 2) ℚ_[q]) :
    EZ q N g = if ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖ then 1 else 0 := rfl

private theorem IB_apply (c : ℚ_[q]) (r : ℝ) (g : GL (Fin 2) ℚ_[q]) :
    IB q c r g = if ‖lr q g - c * lo q g‖ ≤ r * ‖lo q g‖ then 1 else 0 := rfl

private theorem rt_upperN_IB (x c : ℚ_[q]) (r : ℝ) : rt q (upperN q x) (IB q c r) = IB q (c - x) r := by
  funext g
  rw [rt_apply, IB_apply, IB_apply, lo_mul_upperN, lr_mul_upperN,
    show lo q g * x + lr q g - c * lo q g = lr q g - (c - x) * lo q g by ring]

private theorem rt_upperN_EZ {x : ℚ_[q]} {N : ℤ} (hx : ‖x‖ < (q : ℝ) ^ N) : rt q (upperN q x) (EZ q N) = EZ q N := by
  funext g
  rw [rt_apply, EZ_apply, EZ_apply, lo_mul_upperN, lr_mul_upperN]
  by_cases h0 : lo q g = 0
  · simp [h0]
  · have hqN : (0 : ℝ) < (q : ℝ) ^ (-N) := zpow_pos (qR_pos q) _
    have hlo : 0 < ‖lo q g‖ := norm_pos_iff.mpr h0
    have key : ∀ {t : ℚ_[q]}, ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖t‖ → ‖lo q g * x‖ < ‖t‖ := by
      intro t ht
      rw [norm_mul]
      calc ‖lo q g‖ * ‖x‖ < ‖lo q g‖ * (q : ℝ) ^ N := mul_lt_mul_of_pos_left hx hlo
        _ ≤ (q : ℝ) ^ (-N) * ‖t‖ * (q : ℝ) ^ N := mul_le_mul_of_nonneg_right ht (zpow_nonneg (qR_pos q).le _)
        _ = ‖t‖ := by rw [mul_comm ((q:ℝ) ^ (-N)), mul_assoc, ← zpow_add₀ (qR_pos q).ne', neg_add_cancel,
            zpow_zero, mul_one]
    apply ind_congr
    constructor
    · intro h
      have hlt := key h
      have e := norm_add_eq_left_of_lt q (a := lo q g * x + lr q g) (b := -(lo q g * x)) (by rwa [norm_neg])
      rw [← sub_eq_add_neg, add_sub_cancel_left] at e
      rwa [← e] at h
    · intro h
      have hlt := key h
      rw [add_comm, norm_add_eq_left_of_lt q hlt]
      exact h

private theorem EZ_eq_one_sub_IB (N : ℤ) : EZ q N = 1 - IB q 0 ((q : ℝ) ^ (N - 1)) := by
  funext g
  rw [Pi.sub_apply, Pi.one_apply, EZ_apply, IB_apply, zero_mul, sub_zero]
  by_cases h0 : lo q g = 0
  · have hlr : lr q g ≠ 0 := lr_ne_zero_of_lo_eq_zero q h0
    rw [h0, norm_zero, mul_zero, if_pos (by positivity), if_neg (by rw [not_le]; exact norm_pos_iff.mpr hlr)]
    norm_num
  · have hlo : 0 < ‖lo q g‖ := norm_pos_iff.mpr h0
    have hx : ‖lr q g / lo q g‖ = ‖lr q g‖ / ‖lo q g‖ := norm_div _ _

    have hiff : ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖ ↔ ¬ (‖lr q g‖ ≤ (q : ℝ) ^ (N - 1) * ‖lo q g‖) := by
      have e1 : ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖ ↔ (q : ℝ) ^ N ≤ ‖lr q g / lo q g‖ := by
        rw [zpow_neg, le_inv_mul_iff₀ (zpow_pos (qR_pos q) N), hx, le_div_iff₀ hlo]
      have e2 : ‖lr q g‖ ≤ (q : ℝ) ^ (N - 1) * ‖lo q g‖ ↔ ‖lr q g / lo q g‖ ≤ (q : ℝ) ^ (N - 1) := by
        rw [hx, div_le_iff₀ hlo]
      rw [e1, e2, Padic.norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel, not_lt]
    by_cases h : ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖
    · rw [if_pos h, if_neg (hiff.mp h)]
      norm_num
    · rw [if_neg h, if_pos (not_not.mp (fun h'' => h (hiff.mpr h'')))]
      norm_num

private theorem rt_dq_EZ (N : ℤ) : rt q (dq q) (EZ q N) = EZ q (N + 1) := by
  funext g
  rw [rt_apply, EZ_apply, EZ_apply, lo_mul_dq, lr_mul_dq, norm_mul, Padic.norm_p,
    show (q : ℝ) ^ (-N) * (‖lr q g‖ * (q : ℝ)⁻¹) = (q : ℝ) ^ (-(N + 1)) * ‖lr q g‖ by
      rw [zpow_neg, zpow_neg, zpow_add_one₀ (qR_pos q).ne', mul_inv]; ring]

private theorem rt_dq_IB (c : ℚ_[q]) (r : ℝ) : rt q (dq q) (IB q c r) = IB q (c / q) (r * q) := by
  funext g
  rw [rt_apply, IB_apply, IB_apply, lo_mul_dq, lr_mul_dq]
  have hq : (q : ℚ_[q]) ≠ 0 := qp_ne_zero q
  rw [show lr q g * q - c * lo q g = (lr q g - c / q * lo q g) * q by field_simp, norm_mul, Padic.norm_p]
  apply ind_congr
  rw [← div_eq_mul_inv, div_le_iff₀ (qR_pos q), show r * q * ‖lo q g‖ = (r * ‖lo q g‖) * (q : ℝ) by ring]

private theorem rt_pow_succ (h : GL (Fin 2) ℚ_[q]) (F : GL (Fin 2) ℚ_[q] → ℂ) (k : ℕ) :
    rt q (h ^ (k + 1)) F = rt q (h ^ k) (rt q h F) := by
  rw [pow_succ, rt_mul]

private theorem rt_dq_pow_EZ (k : ℕ) (N : ℤ) : rt q (dq q ^ k) (EZ q N) = EZ q (N + k) := by
  induction k generalizing N with
  | zero => simp
  | succ k ih => rw [rt_pow_succ, rt_dq_EZ, ih]; congr 1; push_cast; ring

private theorem rt_dq_pow_IB (k : ℕ) (c : ℚ_[q]) (r : ℝ) :
    rt q (dq q ^ k) (IB q c r) = IB q (c / (q : ℚ_[q]) ^ k) (r * (q : ℝ) ^ k) := by
  induction k generalizing c r with
  | zero => simp
  | succ k ih =>
    rw [rt_pow_succ, rt_dq_IB, ih]
    congr 1
    · rw [div_div]; ring
    · rw [pow_succ]; ring

private theorem rt_w0_IB_zero (N : ℤ) : rt q (w0 q) (IB q 0 ((q : ℝ) ^ (-N))) = EZ q N := by
  funext g
  rw [rt_apply, IB_apply, EZ_apply, lo_mul_w0, lr_mul_w0, zero_mul, sub_zero]

private theorem rt_w0_IB {c : ℚ_[q]} {r : ℝ} (hr : 0 ≤ r) (hc : r < ‖c‖) :
    rt q (w0 q) (IB q c r) = IB q c⁻¹ (r / ‖c‖ ^ 2) := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact (not_lt.mpr hr) hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  funext g
  rw [rt_apply, IB_apply, IB_apply, lo_mul_w0, lr_mul_w0]

  have hrel : lr q g - c⁻¹ * lo q g = -c⁻¹ * (lo q g - c * lr q g) := by field_simp; ring
  apply ind_congr
  constructor
  · intro h
    have hlr : lr q g ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero, norm_zero, mul_zero] at h
      exact (lo_ne_zero_or_lr_ne_zero q g).elim (fun h1 => h1 (norm_le_zero_iff.mp h)) (fun h1 => h1 h0)
    have hlrpos : 0 < ‖lr q g‖ := norm_pos_iff.mpr hlr

    have hdom : ‖lo q g - c * lr q g‖ < ‖c * lr q g‖ := by
      rw [norm_mul]; calc _ ≤ r * ‖lr q g‖ := h
        _ < ‖c‖ * ‖lr q g‖ := mul_lt_mul_of_pos_right hc hlrpos
    have hlo : ‖lo q g‖ = ‖c‖ * ‖lr q g‖ := by
      have := norm_add_eq_left_of_lt q hdom
      rw [add_sub_cancel] at this
      rw [this, norm_mul]
    rw [hrel, norm_mul, norm_neg, norm_inv, hlo]
    rw [show r / ‖c‖ ^ 2 * (‖c‖ * ‖lr q g‖) = ‖c‖⁻¹ * (r * ‖lr q g‖) by field_simp]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hcpos.le)
  · intro h
    have hlo0 : lo q g ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero, norm_zero, mul_zero] at h
      exact (lo_ne_zero_or_lr_ne_zero q g).elim (fun h1 => h1 h0) (fun h1 => h1 (norm_le_zero_iff.mp h))
    have hlopos : 0 < ‖lo q g‖ := norm_pos_iff.mpr hlo0
    have hr' : r / ‖c‖ ^ 2 < ‖c⁻¹‖ := by
      rw [norm_inv, div_lt_iff₀ (by positivity), show ‖c‖⁻¹ * ‖c‖ ^ 2 = ‖c‖ by field_simp]
      exact hc
    have hdom : ‖lr q g - c⁻¹ * lo q g‖ < ‖c⁻¹ * lo q g‖ := by
      rw [norm_mul]; calc _ ≤ r / ‖c‖ ^ 2 * ‖lo q g‖ := h
        _ < ‖c⁻¹‖ * ‖lo q g‖ := mul_lt_mul_of_pos_right hr' hlopos
    have hlr : ‖lr q g‖ = ‖c‖⁻¹ * ‖lo q g‖ := by
      have := norm_add_eq_left_of_lt q hdom
      rw [add_sub_cancel] at this
      rw [this, norm_mul, norm_inv]
    have hrel' : lo q g - c * lr q g = -c * (lr q g - c⁻¹ * lo q g) := by field_simp; ring
    rw [hrel', norm_mul, norm_neg, hlr]
    rw [show r * (‖c‖⁻¹ * ‖lo q g‖) = ‖c‖ * (r / ‖c‖ ^ 2 * ‖lo q g‖) by field_simp]
    exact mul_le_mul_of_nonneg_left h hcpos.le

private theorem norm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[q])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := q) (n : ℤ)
  simpa using this

private theorem sum_IB_tiles {τ : ℚ_[q]} {e : ℤ} (hτ : ‖τ‖ = (q : ℝ) ^ (e + 1)) :
    ∑ a ∈ Finset.range q, IB q ((a : ℚ_[q]) * τ) ((q : ℝ) ^ e) = IB q 0 ((q : ℝ) ^ (e + 1)) := by
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, norm_zero] at hτ; exact (zpow_pos (qR_pos q) _).ne' hτ.symm
  funext g
  rw [Finset.sum_apply]
  simp only [IB_apply, zero_mul, sub_zero]
  by_cases h0 : lo q g = 0
  ·
    have hlr : 0 < ‖lr q g‖ := norm_pos_iff.mpr (lr_ne_zero_of_lo_eq_zero q h0)
    have hF : ∀ (c : ℚ_[q]) (r : ℝ), ¬ (‖lr q g - c * lo q g‖ ≤ r * ‖lo q g‖) := by
      intro c r
      rw [h0, mul_zero, sub_zero, norm_zero, mul_zero, not_le]
      exact hlr
    have hR : ¬ (‖lr q g‖ ≤ (q : ℝ) ^ (e + 1) * ‖lo q g‖) := by
      rw [h0, norm_zero, mul_zero, not_le]
      exact hlr
    rw [if_neg hR]
    exact Finset.sum_eq_zero fun a _ => if_neg (hF _ _)
  have hlo : 0 < ‖lo q g‖ := norm_pos_iff.mpr h0
  set s : ℚ_[q] := lr q g / lo q g with hs
  have hball : ∀ (c : ℚ_[q]) (r : ℝ), (‖lr q g - c * lo q g‖ ≤ r * ‖lo q g‖ ↔ ‖s - c‖ ≤ r) := by
    intro c r
    rw [show lr q g - c * lo q g = (s - c) * lo q g by rw [hs]; field_simp, norm_mul,
      mul_le_mul_iff_left₀ hlo]
  simp only [hball]
  have hR : (‖lr q g‖ ≤ (q : ℝ) ^ (e + 1) * ‖lo q g‖ ↔ ‖s‖ ≤ (q : ℝ) ^ (e + 1)) := by
    rw [hs, norm_div, div_le_iff₀ hlo]
  by_cases hbig : ‖s‖ ≤ (q : ℝ) ^ (e + 1)
  ·
    have hint : ‖s / τ‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.mpr hτ0), hτ]; exact hbig
    set z : ℤ_[q] := ⟨s / τ, hint⟩ with hz
    set a₀ : ℕ := z.appr 1 with ha₀
    have ha₀q : a₀ < q := by simpa using z.appr_lt 1
    have hspec : ‖s / τ - (a₀ : ℚ_[q])‖ ≤ (q : ℝ)⁻¹ := by
      have h1 := PadicInt.appr_spec 1 z
      rw [← ha₀, pow_one] at h1
      have h2 : ‖(z - (a₀ : ℤ_[q]) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(1 : ℕ) : ℤ) := by
        rw [PadicInt.norm_le_pow_iff_mem_span_pow]; simpa using h1
      simp [hz, zpow_neg, zpow_one] at h2
      exact h2
    have hin : ‖s - (a₀ : ℚ_[q]) * τ‖ ≤ (q : ℝ) ^ e := by
      rw [show s - (a₀ : ℚ_[q]) * τ = (s / τ - a₀) * τ by field_simp, norm_mul, hτ]
      calc ‖s / τ - ↑a₀‖ * (q : ℝ) ^ (e + 1) ≤ (q : ℝ)⁻¹ * (q : ℝ) ^ (e + 1) :=
            mul_le_mul_of_nonneg_right hspec (zpow_nonneg (qR_pos q).le _)
        _ = (q : ℝ) ^ e := by
            rw [zpow_add_one₀ (qR_pos q).ne', mul_comm ((q : ℝ) ^ e), ← mul_assoc, inv_mul_cancel₀ (qR_pos q).ne',
              one_mul]

    have huniq : ∀ a ∈ Finset.range q, ‖s - (a : ℚ_[q]) * τ‖ ≤ (q : ℝ) ^ e → a = a₀ := by
      intro a ha h
      have hdiff : ‖((a : ℚ_[q]) - a₀) * τ‖ ≤ (q : ℝ) ^ e := by
        rw [show ((a : ℚ_[q]) - a₀) * τ = (s - a₀ * τ) - (s - a * τ) by ring]
        rw [sub_eq_add_neg]
        refine le_trans (Padic.nonarchimedean _ _) (max_le hin ?_)
        rwa [norm_neg]
      rw [norm_mul, hτ, zpow_add_one₀ (qR_pos q).ne', ← mul_assoc] at hdiff
      have hlt : ‖((a : ℚ_[q]) - a₀)‖ < 1 := by
        have hqe : (0 : ℝ) < (q : ℝ) ^ e := zpow_pos (qR_pos q) e
        have h1 : ‖((a : ℚ_[q]) - a₀)‖ * (q : ℝ) ≤ 1 := by
          refine le_of_mul_le_mul_right ?_ hqe
          rw [one_mul, mul_right_comm]
          exact hdiff
        by_contra hge
        have h2 : (q : ℝ) ≤ ‖((a : ℚ_[q]) - a₀)‖ * (q : ℝ) :=
          le_mul_of_one_le_left (qR_pos q).le (not_lt.mp hge)
        exact absurd (h2.trans h1) (not_le.mpr (one_lt_qR q))
      have hdvd : (q : ℤ) ∣ ((a : ℤ) - a₀) := Padic.norm_intCast_lt_one_iff.mp (by push_cast; exact hlt)
      have ha' : a < q := Finset.mem_range.mp ha
      have h0' := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
      omega
    rw [Finset.sum_eq_single a₀]
    · rw [if_pos hin, if_pos (hR.mpr hbig)]
    · intro a ha hne
      exact if_neg fun h => hne (huniq a ha h)
    · intro h
      exact absurd (Finset.mem_range.mpr ha₀q) h
  ·
    have hout : ∀ a ∈ Finset.range q, ¬ ‖s - (a : ℚ_[q]) * τ‖ ≤ (q : ℝ) ^ e := by
      intro a _ h
      apply hbig
      have hat : ‖(a : ℚ_[q]) * τ‖ ≤ (q : ℝ) ^ (e + 1) := by
        rw [norm_mul, hτ]
        exact mul_le_of_le_one_left (zpow_nonneg (qR_pos q).le _) (norm_natCast_le_one q a)
      have : s = (s - a * τ) + a * τ := by ring
      rw [this]
      refine le_trans (Padic.nonarchimedean _ _) (max_le (le_trans h ?_) hat)
      exact zpow_le_zpow_right₀ (one_lt_qR q).le (by omega)
    rw [Finset.sum_eq_zero (fun a ha => if_neg (hout a ha)), if_neg (fun h => hbig (hR.mp h))]

end SteinbergCell
p2m_reactivate "P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.SteinbergCell"

namespace SteinbergCell

open LocalNewvector

variable (q : ℕ) [Fact q.Prime]

private theorem upperN_mem_Kq {x : ℚ_[q]} (hx : ‖x‖ ≤ 1) : upperN q x ∈ Kq q := by
  apply KM_le_Kq q 0
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  have hone : ((q : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  rw [hone]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [FLT.SmoothVectors.norm_sub_one_entry_le_one_iff, coe_borelElem]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [FLT.SmoothVectors.norm_sub_one_entry_le_one_iff, coe_borelElem_inv]
    fin_cases i <;> fin_cases j <;> simp [hx]

private theorem upperN_mem_KM {L : ℕ} (hL : 1 ≤ L) {x : ℚ_[q]} (hx : ‖x‖ ≤ (q : ℝ) ^ (-(L : ℤ))) :
    upperN q x ∈ KM q L := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hL, coe_borelElem]
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(L : ℤ)) := by positivity
  generalize (q : ℝ) ^ (-(L : ℤ)) = r at hx hpos ⊢
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, hx, hpos]

private theorem norm_eq_one_of_norm_sub_one_le {L : ℕ} (hL : 1 ≤ L) {a : ℚ_[q]} (h : ‖a - 1‖ ≤ (q : ℝ) ^ (-(L : ℤ))) :
    ‖a‖ = 1 :=
  FLT.SmoothVectors.norm_eq_one_of_norm_sub_one_lt_one q (lt_of_le_of_lt h (radius_lt_one' q hL))

private theorem diagE_mem_Kq {a : ℚ_[q]} (ha : ‖a‖ = 1) : diagE q a ∈ Kq q := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  rw [diagE_of_ne_zero q ha0]
  apply KM_le_Kq q 0
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  have hone : ((q : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  rw [hone]
  have hinv : ‖a‖⁻¹ ≤ 1 := by rw [ha, inv_one]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [FLT.SmoothVectors.norm_sub_one_entry_le_one_iff, coe_borelElem]
    fin_cases i <;> fin_cases j <;> simp [ha.le]
  · rw [FLT.SmoothVectors.norm_sub_one_entry_le_one_iff, coe_borelElem_inv]
    fin_cases i <;> fin_cases j <;> simp [hinv, Units.val_inv_eq_inv_val]

private theorem diagE_mem_KM {L : ℕ} (hL : 1 ≤ L) {a : ℚ_[q]} (h : ‖a - 1‖ ≤ (q : ℝ) ^ (-(L : ℤ))) :
    diagE q a ∈ KM q L := by
  have ha : ‖a‖ = 1 := norm_eq_one_of_norm_sub_one_le q hL h
  have ha0 : a ≠ 0 := by intro h0; rw [h0, norm_zero] at ha; exact zero_ne_one ha
  rw [diagE_of_ne_zero q ha0, FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hL, coe_borelElem]
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(L : ℤ)) := by positivity
  generalize (q : ℝ) ^ (-(L : ℤ)) = r at h hpos ⊢
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, h, hpos]

private theorem upperN_mul (x y : ℚ_[q]) : upperN q x * upperN q y = upperN q (x + y) := by
  rw [borelElem_mul]
  congr 1 <;> simp [add_comm]

private theorem diagE_mul {a b : ℚ_[q]} (ha : a ≠ 0) (hb : b ≠ 0) : diagE q a * diagE q b = diagE q (a * b) := by
  rw [diagE_of_ne_zero q ha, diagE_of_ne_zero q hb, diagE_of_ne_zero q (mul_ne_zero ha hb), borelElem_mul]
  congr 1
  · exact Units.ext rfl
  · simp
  · simp

private theorem upperN_mul_diagE (x : ℚ_[q]) {a : ℚ_[q]} (ha : a ≠ 0) :
    upperN q x * diagE q a = diagE q a * upperN q (x / a) := by
  rw [diagE_of_ne_zero q ha]
  refine Units.ext ?_
  simp only [Units.val_mul, coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try (field_simp))

private theorem diagE_mul_lowerU {α c : ℚ_[q]} {k : ℕ} (hα : α ≠ 0) (hc : c = (q : ℚ_[q]) ^ k * α) :
    diagE q α * lowerU q c = lowerU q ((q : ℚ_[q]) ^ k) * diagE q α := by
  rw [diagE_of_ne_zero q hα]
  refine Units.ext ?_
  simp only [Units.val_mul, coe_borelElem, coe_lowerU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, mul_comm]

private theorem w0_mul_w0 : w0 q * w0 q = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_w0, Units.val_one, Matrix.mul_fin_two, Matrix.one_fin_two]; simp

private theorem lowerU_zero : lowerU q 0 = 1 := by
  refine Units.ext ?_
  rw [coe_lowerU, Units.val_one, Matrix.one_fin_two]

@[scoped simp] private theorem upperN_zero : upperN q 0 = 1 := borelElem_one q

private theorem diagE_one : diagE q 1 = 1 := by
  rw [diagE_of_ne_zero q one_ne_zero]
  have : Units.mk0 (1 : ℚ_[q]) one_ne_zero = 1 := Units.ext rfl
  rw [this, borelElem_one]

private def ref (L j : ℕ) : GL (Fin 2) ℚ_[q] :=
  if j = 0 then w0 q else if j < L then lowerU q ((q : ℚ_[q]) ^ j) else 1

private def IsRadial (L : ℕ) (Φ : GL (Fin 2) ℚ_[q] → ℂ) : Prop :=
  (∀ b g, IsUpper q b → Φ (b * g) = Φ g) ∧ (∀ x : ℚ_[q], ‖x‖ ≤ 1 → rt q (upperN q x) Φ = Φ) ∧
    (∀ a : ℚ_[q], ‖a‖ = 1 → rt q (diagE q a) Φ = Φ) ∧ ∀ m ∈ KM q L, rt q m Φ = Φ

variable {q} in
private theorem IsRadial.upper {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (h : IsRadial q L Φ) :
    ∀ b g, IsUpper q b → Φ (b * g) = Φ g := h.1

variable {q} in
private theorem IsRadial.transl {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (h : IsRadial q L Φ) :
    ∀ x : ℚ_[q], ‖x‖ ≤ 1 → rt q (upperN q x) Φ = Φ := h.2.1

variable {q} in
private theorem IsRadial.torus {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (h : IsRadial q L Φ) :
    ∀ a : ℚ_[q], ‖a‖ = 1 → rt q (diagE q a) Φ = Φ := h.2.2.1

variable {q} in
private theorem IsRadial.level {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (h : IsRadial q L Φ) : ∀ m ∈ KM q L, rt q m Φ = Φ :=
  h.2.2.2

private theorem rt_diagE_EZ {a : ℚ_[q]} (ha : ‖a‖ = 1) (N : ℤ) : rt q (diagE q a) (EZ q N) = EZ q N := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  funext g
  rw [rt_apply, EZ_apply, EZ_apply, lo_mul_diagE q g a ha0, lr_mul_diagE q g a ha0, norm_mul, ha, mul_one]

private theorem one_lt_q_zpow {N : ℤ} (hN : 1 ≤ N) : (1 : ℝ) < (q : ℝ) ^ N :=
  one_lt_zpow₀ (one_lt_qR q) (by omega)

private theorem isRadial_EZ {L i : ℕ} (hi : 1 ≤ i) (hiL : i ≤ L) : IsRadial q L (EZ q (i : ℤ)) := by
  refine ⟨fun b g hb => EZ_upper_mul q hb g, fun x hx => ?_, fun a ha => rt_diagE_EZ q ha _, fun m hm => ?_⟩
  · exact rt_upperN_EZ q (lt_of_le_of_lt hx (one_lt_q_zpow q (by exact_mod_cast hi)))
  · have hm' : m ∈ KM q i := FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q hiL hm
    rw [← E_eq_EZ q hi]
    funext g
    exact E_mul_KM q hm' g

private theorem EZ_ref {L i j : ℕ} (hi : 1 ≤ i) (hiL : i ≤ L) (hj : j ≤ L) :
    EZ q (i : ℤ) (ref q L j) = if i ≤ j then 1 else 0 := by
  unfold ref
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl, EZ_apply, if_neg (by omega : ¬ (i ≤ 0))]
    rw [if_neg]
    simp [lo, lr]
  · rw [if_neg hj0]
    by_cases hjL : j < L
    · rw [if_pos hjL, EZ_apply]
      simp only [lo, lr, coe_lowerU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', norm_one, mul_one, norm_pow, Padic.norm_p]
      rw [inv_pow, ← zpow_natCast, ← zpow_neg]
      by_cases hij : i ≤ j
      · rw [if_pos hij, if_pos]
        exact zpow_le_zpow_right₀ (one_lt_qR q).le (by omega)
      · rw [if_neg hij, if_neg]
        rw [not_le]
        exact zpow_lt_zpow_right₀ (one_lt_qR q) (by omega)
    · have hjL' : j = L := by omega
      rw [if_neg hjL, EZ_apply, if_pos (by omega : i ≤ j), if_pos]
      simp [lo]

private theorem exists_ref {L : ℕ} (hL : 1 ≤ L) (g : GL (Fin 2) ℚ_[q]) :
    ∃ j, j ≤ L ∧ ∀ Φ, IsRadial q L Φ → Φ g = Φ (ref q L j) := by
  by_cases hcmp : ‖lr q g‖ ≤ ‖lo q g‖
  ·
    have hlo : lo q g ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hcmp
      exact lr_ne_zero_of_lo_eq_zero q h0 (norm_le_zero_iff.mp hcmp)
    set d : ℚ_[q] := lr q g / lo q g with hd
    have hdn : ‖d‖ ≤ 1 := by rw [hd, norm_div, div_le_one (norm_pos_iff.mpr hlo)]; exact hcmp
    have hb : IsUpper q (g * upperN q (-d) * w0 q) := by
      unfold IsUpper
      rw [lo_mul_w0, lr_mul_upperN, hd]
      field_simp
      ring
    refine ⟨0, Nat.zero_le _, fun Φ hΦ => ?_⟩
    have hg : g = (g * upperN q (-d) * w0 q) * (w0 q * upperN q d) := by
      rw [show g * upperN q (-d) * w0 q * (w0 q * upperN q d)
          = g * upperN q (-d) * (w0 q * w0 q) * upperN q d by simp only [mul_assoc], w0_mul_w0, mul_one,
        mul_assoc, upperN_mul, neg_add_cancel, upperN_zero, mul_one]
    rw [hg, IsRadial.upper hΦ _ _ hb]
    unfold ref
    rw [if_pos rfl]
    have := congrFun (IsRadial.transl hΦ d hdn) (w0 q)
    rw [rt_apply] at this
    exact this
  ·
    rw [not_le] at hcmp
    have hlr : lr q g ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hcmp; exact (not_lt.mpr (norm_nonneg _)) hcmp
    obtain ⟨b, hb, hg⟩ := exists_upper_mul_lowerU q g hlr
    set c : ℚ_[q] := lo q g / lr q g with hc
    have hcn : ‖c‖ < 1 := by rw [hc, norm_div, div_lt_one (norm_pos_iff.mpr hlr)]; exact hcmp
    by_cases hc0 : c = 0
    · refine ⟨L, le_rfl, fun Φ hΦ => ?_⟩
      rw [hg, hc0, lowerU_zero, IsRadial.upper hΦ _ _ hb]
      unfold ref
      rw [if_neg (by omega), if_neg (lt_irrefl L)]
    ·
      set k : ℤ := c.valuation with hk
      have hck : ‖c‖ = (q : ℝ) ^ (-k) := Padic.norm_eq_zpow_neg_valuation hc0
      have hk1 : 1 ≤ k := by
        have : (q : ℝ) ^ (-k) < (q : ℝ) ^ (0 : ℤ) := by rw [zpow_zero, ← hck]; exact hcn
        have := (zpow_lt_zpow_iff_right₀ (one_lt_qR q)).mp this
        omega
      by_cases hkL : (L : ℤ) ≤ k
      ·
        refine ⟨L, le_rfl, fun Φ hΦ => ?_⟩
        have hmem : lowerU q c ∈ KM q L := by
          apply lowerU_mem_KM q hL
          rw [hck]
          exact zpow_le_zpow_right₀ (one_lt_qR q).le (by omega)
        rw [hg, IsRadial.upper hΦ _ _ hb]
        have := congrFun (IsRadial.level hΦ _ hmem) 1
        rw [rt_apply, one_mul] at this
        rw [this]
        unfold ref
        rw [if_neg (by omega), if_neg (lt_irrefl L)]
      ·
        rw [not_le] at hkL
        set kn : ℕ := k.toNat with hkn
        have hknk : (kn : ℤ) = k := Int.toNat_of_nonneg (by omega)
        have hkn1 : 1 ≤ kn := by omega
        have hknL : kn < L := by omega
        set α : ℚ_[q] := c / (q : ℚ_[q]) ^ kn with hα
        have hqk : ((q : ℚ_[q]) ^ kn) ≠ 0 := pow_ne_zero _ (qp_ne_zero q)
        have hαn : ‖α‖ = 1 := by
          rw [hα, norm_div, norm_pow, Padic.norm_p, hck, inv_pow, ← zpow_natCast, ← zpow_neg, hknk, div_self]
          exact (zpow_pos (qR_pos q) _).ne'
        have hα0 : α ≠ 0 := by intro h; rw [h, norm_zero] at hαn; exact zero_ne_one hαn
        have hcα : c = (q : ℚ_[q]) ^ kn * α := by rw [hα]; field_simp
        refine ⟨kn, hknL.le, fun Φ hΦ => ?_⟩
        rw [hg, IsRadial.upper hΦ _ _ hb]

        rw [← IsRadial.upper hΦ (diagE q α) (lowerU q c) (isUpper_diagE q α), diagE_mul_lowerU q hα0 hcα]
        have := congrFun (IsRadial.torus hΦ α hαn) (lowerU q ((q : ℚ_[q]) ^ kn))
        rw [rt_apply] at this
        rw [this]
        unfold ref
        rw [if_neg (by omega), if_pos hknL]

private theorem radial_expansion {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : IsRadial q L Φ) :
    Φ = (fun _ => Φ (ref q L 0)) +
      ∑ i ∈ Finset.range L, (Φ (ref q L (i + 1)) - Φ (ref q L i)) • EZ q ((i + 1 : ℕ) : ℤ) := by
  funext g
  obtain ⟨j, hjL, hj⟩ := exists_ref q hL g
  rw [hj Φ hΦ, Pi.add_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hE : ∀ i ∈ Finset.range L, EZ q ((i + 1 : ℕ) : ℤ) g = if i + 1 ≤ j then 1 else 0 := by
    intro i hi
    have hi' : i + 1 ≤ L := Finset.mem_range.mp hi
    rw [hj _ (isRadial_EZ q (Nat.succ_pos i) hi'), EZ_ref q (Nat.succ_pos i) hi' hjL]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hE i hi])]

  rw [← Finset.sum_range_add_sum_Ico _ hjL]
  rw [Finset.sum_eq_zero (s := Finset.Ico j L) (fun i hi => by
    rw [Finset.mem_Ico] at hi
    rw [if_neg (by omega), mul_zero])]
  rw [add_zero, Finset.sum_congr rfl (fun i hi => by
    rw [if_pos (by have := Finset.mem_range.mp hi; omega), mul_one])]
  rw [Finset.sum_range_sub (fun i => Φ (ref q L i)) j]
  ring

section Heart

variable (S : Submodule ℂ (GL (Fin 2) ℚ_[q] → ℂ)) (hS : ∀ h, ∀ F ∈ S, rt q h F ∈ S)
include hS

omit hS in

private theorem exists_first_jump {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : IsRadial q L Φ)
    (hnc : ∃ g, Φ g ≠ Φ 1) :
    ∃ m, m < L ∧ Φ (ref q L (m + 1)) ≠ Φ (ref q L m) ∧ ∀ i, i < m → Φ (ref q L (i + 1)) = Φ (ref q L i) := by
  classical
  have hexp := radial_expansion q hL hΦ
  have hjump : ∃ i, i < L ∧ Φ (ref q L (i + 1)) ≠ Φ (ref q L i) := by
    by_contra hno
    push Not at hno
    obtain ⟨g, hg⟩ := hnc
    apply hg
    have hall : ∀ i ∈ Finset.range L, (Φ (ref q L (i + 1)) - Φ (ref q L i)) = 0 := fun i hi =>
      sub_eq_zero.mpr (hno i (Finset.mem_range.mp hi))
    have hΦc : Φ = fun _ => Φ (ref q L 0) := by
      rw [hexp, Finset.sum_eq_zero (fun i hi => by rw [hall i hi, zero_smul]), add_zero]
    exact (congrFun hΦc g).trans (congrFun hΦc 1).symm
  refine ⟨Nat.find hjump, (Nat.find_spec hjump).1, (Nat.find_spec hjump).2, fun i hi => ?_⟩
  have := Nat.find_min hjump hi
  push Not at this
  exact this (lt_trans hi (Nat.find_spec hjump).1)

omit hS in

private theorem rt_sub_self_of_expansion {ι : Type*} (s : Finset ι) (h : GL (Fin 2) ℚ_[q]) (Φ : GL (Fin 2) ℚ_[q] → ℂ)
    (c : ℂ) (e : ι → ℂ) (Z : ι → GL (Fin 2) ℚ_[q] → ℂ) (hexp : Φ = (fun _ => c) + ∑ i ∈ s, e i • Z i) :
    rt q h Φ - Φ = ∑ i ∈ s, e i • (rt q h (Z i) - Z i) := by
  subst hexp
  rw [rt_add, rt_sum, show rt q h (fun _ : GL (Fin 2) ℚ_[q] => c) = fun _ => c from rfl, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rt_smul, smul_sub]

private theorem diff_balls_mem {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦS : Φ ∈ S) (hΦ : IsRadial q L Φ)
    {m : ℕ} (hmL : m < L) (hjump : Φ (ref q L (m + 1)) ≠ Φ (ref q L m))
    (hmin : ∀ i, i < m → Φ (ref q L (i + 1)) = Φ (ref q L i)) :
    IB q 0 ((q : ℝ) ^ ((m : ℤ) + 1 - 1)) - IB q (-((q : ℚ_[q]) ^ (-((m : ℤ) + 1)))) ((q : ℝ) ^ ((m : ℤ) + 1 - 1))
      ∈ S := by
  classical
  set β : ℚ_[q] := (q : ℚ_[q]) ^ (-((m : ℤ) + 1)) with hβ
  set ρ : ℝ := (q : ℝ) ^ ((m : ℤ) + 1 - 1) with hρ
  have hβn : ‖β‖ = (q : ℝ) ^ ((m : ℤ) + 1) := by rw [hβ, Padic.norm_p_zpow, neg_neg]
  have hDD := rt_sub_self_of_expansion q (Finset.range L) (upperN q β) Φ (Φ (ref q L 0))
    (fun i => Φ (ref q L (i + 1)) - Φ (ref q L i)) (fun i => EZ q ((i + 1 : ℕ) : ℤ)) (radial_expansion q hL hΦ)
  have hsingle : ∑ i ∈ Finset.range L, (fun i => Φ (ref q L (i + 1)) - Φ (ref q L i)) i •
      (rt q (upperN q β) ((fun i => EZ q ((i + 1 : ℕ) : ℤ)) i) - (fun i => EZ q ((i + 1 : ℕ) : ℤ)) i)
      = (Φ (ref q L (m + 1)) - Φ (ref q L m)) • (IB q 0 ρ - IB q (-β) ρ) := by
    rw [Finset.sum_eq_single m]
    · have hE : EZ q ((m + 1 : ℕ) : ℤ) = 1 - IB q 0 ρ := by
        rw [EZ_eq_one_sub_IB]; congr 2; try push_cast
      have hrtE : rt q (upperN q β) (EZ q ((m + 1 : ℕ) : ℤ)) = 1 - IB q (-β) ρ := by
        rw [hE, rt_sub, rt_upperN_IB, zero_sub]; rfl
      beta_reduce
      rw [hrtE, hE]
      congr 1
      abel
    · intro i _ hne
      beta_reduce
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [hmin i hlt, sub_self, zero_smul]
      · rw [rt_upperN_EZ q (by rw [hβn]; exact zpow_lt_zpow_right₀ (one_lt_qR q) (by push_cast; omega)), sub_self,
          smul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hmL) h
  rw [hsingle] at hDD
  have hmem : rt q (upperN q β) Φ - Φ ∈ S := S.sub_mem (hS _ _ hΦS) hΦS
  rw [hDD] at hmem
  have hne : Φ (ref q L (m + 1)) - Φ (ref q L m) ≠ 0 := sub_ne_zero.mpr hjump
  have := S.smul_mem (Φ (ref q L (m + 1)) - Φ (ref q L m))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

private theorem E_two_sub_ball_mem {J : ℕ}
    (hD : IB q 0 ((q : ℝ) ^ ((J : ℤ) - 1)) - IB q (-((q : ℚ_[q]) ^ (-(J : ℤ)))) ((q : ℝ) ^ ((J : ℤ) - 1)) ∈ S) :
    ∃ c : ℚ_[q], ‖c‖ = (q : ℝ) ∧ EZ q 2 - IB q c 1 ∈ S := by
  set β : ℚ_[q] := (q : ℚ_[q]) ^ (-(J : ℤ)) with hβ
  set ρ : ℝ := (q : ℝ) ^ ((J : ℤ) - 1) with hρ
  have hβn : ‖β‖ = (q : ℝ) ^ (J : ℤ) := by rw [hβ, Padic.norm_p_zpow, neg_neg]
  have hρβ : ρ < ‖-β‖ := by rw [norm_neg, hβn, hρ]; exact zpow_lt_zpow_right₀ (one_lt_qR q) (by omega)
  refine ⟨(-β)⁻¹ / (q : ℚ_[q]) ^ (J + 1), ?_, ?_⟩
  · rw [norm_div, norm_inv, norm_neg, hβn, norm_pow, Padic.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_neg,
      ← zpow_sub₀ (qR_pos q).ne', show (-(J : ℤ) - -((J + 1 : ℕ) : ℤ)) = 1 by push_cast; ring, zpow_one]
  · have hY : rt q (dq q ^ (J + 1)) (rt q (w0 q) (IB q 0 ρ - IB q (-β) ρ))
        = EZ q 2 - IB q ((-β)⁻¹ / (q : ℚ_[q]) ^ (J + 1)) 1 := by
      rw [rt_sub, rt_sub, show ρ = (q : ℝ) ^ (-(1 - (J : ℤ))) by rw [hρ]; congr 1; ring, rt_w0_IB_zero,
        rt_w0_IB q (zpow_nonneg (qR_pos q).le _) (by rw [show -(1 - (J : ℤ)) = (J : ℤ) - 1 by ring]; exact hρβ),
        rt_dq_pow_EZ, rt_dq_pow_IB]
      congr 1
      · congr 1; push_cast; ring
      · congr 1
        rw [norm_neg, hβn, ← zpow_natCast ((q : ℝ) ^ (J : ℤ)) 2, ← zpow_mul, ← zpow_natCast (q : ℝ) (J + 1),
          div_mul_eq_mul_div, ← zpow_add₀ (qR_pos q).ne', div_eq_one_iff_eq (zpow_ne_zero _ (qR_pos q).ne')]
        congr 1; push_cast; ring
    rw [← hY]
    exact hS _ _ (hS _ _ hD)

private theorem V_mem {c : ℚ_[q]} (hc : ‖c‖ = (q : ℝ)) (hY : EZ q 2 - IB q c 1 ∈ S) :
    (q + 1 : ℂ) • EZ q 2 - 1 ∈ S := by
  set τ : ℚ_[q] := (q : ℚ_[q])⁻¹ with hτ
  have hτn : ‖τ‖ = (q : ℝ) ^ ((0 : ℤ) + 1) := by rw [hτ, norm_inv, Padic.norm_p, inv_inv, zero_add, zpow_one]
  have hq2 : (q : ℝ) < (q : ℝ) ^ (2 : ℤ) := by rw [zpow_two]; exact lt_mul_self (one_lt_qR q)
  have hYa : ∀ a : ℕ, a < q → rt q (upperN q (c - a * τ)) (EZ q 2 - IB q c 1) = EZ q 2 - IB q (a * τ) 1 := by
    intro a _
    rw [rt_sub, rt_upperN_IB, rt_upperN_EZ q]
    · congr 2; ring
    · rw [sub_eq_add_neg]
      refine lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt (by rw [hc]; exact hq2) ?_)
      rw [norm_neg, norm_mul, hτn, zero_add, zpow_one]
      calc ‖(a : ℚ_[q])‖ * q ≤ 1 * q := mul_le_mul_of_nonneg_right (norm_natCast_le_one q a) (qR_pos q).le
        _ < (q : ℝ) ^ (2 : ℤ) := by rw [one_mul]; exact hq2
  have hmem : ∑ a ∈ Finset.range q, rt q (upperN q (c - a * τ)) (EZ q 2 - IB q c 1) ∈ S :=
    S.sum_mem fun a _ => hS _ _ hY
  rw [Finset.sum_congr rfl (fun a ha => hYa a (Finset.mem_range.mp ha)), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range] at hmem
  have htile := sum_IB_tiles q (e := 0) hτn
  rw [zpow_zero, zero_add, zpow_one] at htile
  rw [htile] at hmem
  have hE2 : EZ q 2 = 1 - IB q 0 (q : ℝ) := by
    rw [EZ_eq_one_sub_IB]; norm_num
  have hI : IB q 0 (q : ℝ) = 1 - EZ q 2 := by rw [hE2]; abel
  rw [hI] at hmem
  have e : (q + 1 : ℂ) • EZ q 2 - 1 = q • EZ q 2 - (1 - EZ q 2) := by
    rw [add_smul, one_smul, ← Nat.cast_smul_eq_nsmul ℂ]
    abel
  rw [e]
  exact hmem

private theorem Y0_mem {c : ℚ_[q]} (hc : ‖c‖ = (q : ℝ)) (hY : EZ q 2 - IB q c 1 ∈ S) : EZ q 2 + EZ q 1 - 1 ∈ S := by
  have hq2 : (q : ℝ) < (q : ℝ) ^ (2 : ℤ) := by rw [zpow_two]; exact lt_mul_self (one_lt_qR q)
  have hmem := hS (upperN q c) _ hY
  rw [rt_sub, rt_upperN_IB, rt_upperN_EZ q (by rw [hc]; exact hq2), sub_self] at hmem
  have hE1 : EZ q 1 = 1 - IB q 0 1 := by rw [EZ_eq_one_sub_IB]; norm_num
  have hI : IB q 0 1 = 1 - EZ q 1 := by rw [hE1]; abel
  rw [hI] at hmem
  have e : EZ q 2 + EZ q 1 - 1 = EZ q 2 - (1 - EZ q 1) := by abel
  rw [e]
  exact hmem

omit hS in
omit hS in
private theorem rt_one' (h : GL (Fin 2) ℚ_[q]) : rt q h (1 : GL (Fin 2) ℚ_[q] → ℂ) = 1 := rfl

private theorem E_two_mem_of_VY (hV : (q + 1 : ℂ) • EZ q 2 - 1 ∈ S) (hY0 : EZ q 2 + EZ q 1 - 1 ∈ S) : E q 2 ∈ S := by
  have hXS : EZ q 1 - EZ q 3 ∈ S := by
    have hmem := S.sub_mem hY0 (hS (dq q) _ hY0)
    rw [rt_sub, rt_add, rt_dq_EZ, rt_dq_EZ, rt_one'] at hmem
    have e : EZ q 1 - EZ q 3 = EZ q 2 + EZ q 1 - 1 - (EZ q (2 + 1) + EZ q (1 + 1) - 1) := by norm_num; abel
    rw [e]
    exact hmem
  have hX'S : (q + 1 : ℂ) • (EZ q 2 - EZ q 3) ∈ S := by
    have hmem := S.sub_mem hV (hS (dq q) _ hV)
    rw [rt_sub, rt_smul, rt_dq_EZ, rt_one'] at hmem
    have e : (q + 1 : ℂ) • (EZ q 2 - EZ q 3) = (q + 1 : ℂ) • EZ q 2 - 1 - ((q + 1 : ℂ) • EZ q (2 + 1) - 1) := by
      norm_num; rw [smul_sub]; try abel
    rw [e]
    exact hmem
  have hq1 : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hqm1 : ((q : ℂ) - 1) ≠ 0 := by
    have hq : 1 < q := (Fact.out : q.Prime).one_lt
    intro h
    have h' : (q : ℂ) = 1 := sub_eq_zero.mp h
    have : (q : ℕ) = 1 := by exact_mod_cast h'
    omega
  have hfinal : EZ q 2 = ((q : ℂ) - 1)⁻¹ • (((q + 1 : ℂ) • EZ q 2 - 1) - (EZ q 2 + EZ q 1 - 1) + (EZ q 1 - EZ q 3)
      - (q + 1 : ℂ)⁻¹ • ((q + 1 : ℂ) • (EZ q 2 - EZ q 3))) := by
    rw [smul_smul, inv_mul_cancel₀ hq1, one_smul]
    funext g
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    field_simp
    ring
  rw [E_eq_EZ q (by norm_num : 1 ≤ 2), show ((2 : ℕ) : ℤ) = 2 by norm_num, hfinal]
  exact S.smul_mem _ (S.sub_mem (S.add_mem (S.sub_mem hV hY0) hXS) (S.smul_mem _ hX'S))

private theorem E_two_mem_of_radial {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦS : Φ ∈ S)
    (hΦ : IsRadial q L Φ) (hΦnc : ∃ g, Φ g ≠ Φ 1) : E q 2 ∈ S := by
  obtain ⟨m, hmL, hjump, hmin⟩ := exists_first_jump q hL hΦ hΦnc
  have hD := diff_balls_mem q S hS hL hΦS hΦ hmL hjump hmin
  rw [show (m : ℤ) + 1 - 1 = ((m + 1 : ℕ) : ℤ) - 1 by push_cast; ring,
    show -((m : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring] at hD
  obtain ⟨c, hc, hY⟩ := E_two_sub_ball_mem q S hS hD
  exact E_two_mem_of_VY q S hS (V_mem q S hS hc hY) (Y0_mem q S hS hc hY)

private theorem E_mem_of_E_two_mem (h2 : E q 2 ∈ S) {L : ℕ} (hL : 2 ≤ L) : E q L ∈ S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hL
  have := hS (dq q ^ k) _ h2
  rw [E_eq_EZ q (by norm_num : 1 ≤ 2), rt_dq_pow_EZ] at this
  rw [E_eq_EZ q (by omega)]
  convert this using 2
  rfl

end Heart
p2m_reactivate "P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.SteinbergCell"

end SteinbergCell
p2m_reactivate "P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.SteinbergCell"

end
p2m_reactivate "P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.SteinbergCell"

open SteinbergCell in

theorem solution (p : ℕ) [Fact p.Prime] (S : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ))
    (hS : ∀ (h : GL (Fin 2) ℚ_[p]), ∀ F ∈ S, (fun g => F (g * h)) ∈ S)
    (Φ : GL (Fin 2) ℚ_[p] → ℂ) (hΦS : Φ ∈ S)
    (hΦB : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → Φ (b * g) = Φ g)
    {L : ℕ} (hL : 1 ≤ L)
    (hΦK : ∀ m ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p L, (fun g => Φ (g * m)) = Φ)
    (hΦN : ∀ x : ℚ_[p], ‖x‖ ≤ 1 → (fun g => Φ (g * LocalNewvector.borelElem p 1 1 x)) = Φ)
    (hΦT : ∀ a : ℚ_[p]ˣ, ‖(a : ℚ_[p])‖ = 1 →
      (fun g => Φ (g * LocalNewvector.borelElem p a 1 0)) = Φ)
    (hΦnc : ∃ g : GL (Fin 2) ℚ_[p], Φ g ≠ Φ 1) (M : ℕ) (hM : 2 ≤ M) :
    Set.indicator {g : GL (Fin 2) ℚ_[p] | ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖
        ≤ (p : ℝ) ^ (-(M : ℤ)) * ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖} 1 ∈ S := by
  have hT : ∀ a : ℚ_[p], ‖a‖ = 1 → rt p (diagE p a) Φ = Φ := by
    intro a ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      exact zero_ne_one ha
    rw [diagE_of_ne_zero p ha0]
    exact hΦT (Units.mk0 a ha0) ha
  have hrad : IsRadial p L Φ := ⟨hΦB, hΦN, hT, hΦK⟩
  have h2 : E p 2 ∈ S := E_two_mem_of_radial p S hS hL hΦS hrad hΦnc
  have hE : E p M ∈ S := E_mem_of_E_two_mem p S hS h2 hM
  rw [E_eq_EZ p (by omega)] at hE
  have hEq : Set.indicator {g : GL (Fin 2) ℚ_[p] | ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖
      ≤ (p : ℝ) ^ (-(M : ℤ)) * ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖} (1 : GL (Fin 2) ℚ_[p] → ℂ)
        = EZ p (M : ℤ) := by
    funext g
    rw [Set.indicator_apply, Pi.one_apply]
    unfold EZ
    exact ind_congr Iff.rfl
  rw [hEq]
  exact hE

end S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
end P2MW
export P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable (solution)
