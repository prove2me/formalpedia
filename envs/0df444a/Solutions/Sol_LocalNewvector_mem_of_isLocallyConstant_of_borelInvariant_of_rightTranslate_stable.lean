-- Prove2me | solution 1 for LocalNewvector.mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4a9b082e-70f1-543e-b4e5-8233e9de85a4

import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace SteinbergGenFI

open Matrix

variable (q : ℕ) [Fact q.Prime]

private theorem glMap_padicInt_injective :
    Function.Injective (GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])) := by
  apply Units.map_injective
  intro A B hAB
  ext i j
  have hf : Function.Injective (algebraMap ℤ_[q] ℚ_[q]) := IsFractionRing.injective ℤ_[q] ℚ_[q]
  apply hf
  have := congrArg (fun M => M i j) hAB
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe] using this

variable (a : ℕ)

private noncomputable def liftK1Fun (k : LocalNewvector.padicK1 q a) : GL (Fin 2) ℤ_[q] :=
  k.2.choose

private theorem glMap_liftK1Fun (k : LocalNewvector.padicK1 q a) :
    GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) (liftK1Fun q a k) = k.1 :=
  (k.2.choose_spec).1

@[simps]
private noncomputable def liftK1 : ↥(LocalNewvector.padicK1 q a) →* GL (Fin 2) ℤ_[q] where
  toFun := liftK1Fun q a
  map_one' := by
    apply glMap_padicInt_injective q
    rw [glMap_liftK1Fun, map_one]
    rfl
  map_mul' := by
    intro k₁ k₂
    apply glMap_padicInt_injective q
    rw [map_mul, glMap_liftK1Fun, glMap_liftK1Fun, glMap_liftK1Fun]
    rfl

private noncomputable def reductionHom (m : ℕ) :
    ↥(LocalNewvector.padicK1 q a) →* GL (Fin 2) (ZMod (q ^ m)) :=
  (GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZModPow m)).comp (liftK1 q a)

private theorem entry_norm_le_of_mem_ker_reductionHom (m : ℕ) (k : LocalNewvector.padicK1 q a)
    (hk : k ∈ (reductionHom q a m).ker) (i j : Fin 2) :
    ‖((k.1 : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j‖ ≤ (q : ℝ) ^ (-(m : ℤ)) := by

  have hred : GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZModPow m) (liftK1Fun q a k) = 1 := by
    have hk' : (reductionHom q a m) k = 1 := MonoidHom.mem_ker.mp hk
    simpa [reductionHom, liftK1_apply, MonoidHom.comp_apply] using hk'

  have hentry : (PadicInt.toZModPow m) ((liftK1Fun q a k : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j := by
    have h := congrArg
      (fun g : GL (Fin 2) (ZMod (q ^ m)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j) hred
    simpa [GeneralLinearGroup.map_apply] using h

  have hk1 : (((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j
      = (((liftK1Fun q a k : Matrix (Fin 2) (Fin 2) ℤ_[q]) - 1) i j : ℚ_[q]) := by
    rw [← glMap_liftK1Fun q a k]
    simp only [GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, Matrix.sub_apply,
      Matrix.one_apply, apply_ite ((↑·) : ℤ_[q] → ℚ_[q]), PadicInt.coe_one, PadicInt.coe_zero,
      PadicInt.coe_sub]
  rw [hk1, ← PadicInt.norm_def, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, Matrix.sub_apply, map_sub, hentry]
  simp only [Matrix.one_apply, apply_ite (PadicInt.toZModPow (p := q) m), map_one, map_zero,
    sub_self]

private theorem finiteIndex_gl2CongruenceSubgroup_subgroupOf_padicK1 (m a : ℕ) :
    ((FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf
      (LocalNewvector.padicK1 q a)).FiniteIndex := by

  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (Nat.Prime.ne_zero Fact.out)⟩
  haveI : Finite (reductionHom q a m).range := Subtype.finite
  haveI hker : (reductionHom q a m).ker.FiniteIndex := Subgroup.finiteIndex_ker _

  refine Subgroup.finiteIndex_of_le (H := (reductionHom q a m).ker) ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf, FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  refine ⟨entry_norm_le_of_mem_ker_reductionHom q a m k hk, ?_⟩

  have hkinv : k⁻¹ ∈ (reductionHom q a m).ker := (reductionHom q a m).ker.inv_mem hk
  have := entry_norm_le_of_mem_ker_reductionHom q a m k⁻¹ hkinv
  simpa using this

end SteinbergGenFI

namespace SteinbergGen

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

private theorem apply_upper_mul_of_mem_principalSeries {μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ} {f : GL (Fin 2) ℚ_[q] → ℂ}
    (hf : f ∈ principalSeries q μ₁ μ₂) {b : GL (Fin 2) ℚ_[q]} (hb : IsUpper q b) :
    ∃ c : ℂ, ∀ g, f (b * g) = c * f g := by
  obtain ⟨a₁, a₂, x, rfl⟩ := exists_borelElem_eq q hb
  exact ⟨_, fun g => apply_borelElem_mul_of_mem_principalSeries q hf a₁ a₂ x g⟩

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

private theorem mul_mem_Omega_of_mem_Kq {M : ℕ} {g h : GL (Fin 2) ℚ_[q]} (hg : g ∈ Omega q M) (hhK : h ∈ Kq q)
    (hh : h ∈ Omega q M) : g * h ∈ Omega q M := by
  obtain ⟨b, m, hb, hm, rfl⟩ := hg
  obtain ⟨b', m', hb', hm', rfl⟩ := hh

  have hb'K : b' ∈ Kq q := by
    have : b' * m' * m'⁻¹ ∈ Kq q := (Kq q).mul_mem hhK ((Kq q).inv_mem (KM_le_Kq q M hm'))
    rwa [mul_inv_cancel_right] at this
  refine ⟨b * b', b'⁻¹ * m * b' * m', isUpper_mul q hb hb',
    (KM q M).mul_mem (conj_mem_KM' q hb'K hm) hm', ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left]

private theorem inv_mem_Omega_of_mem_Kq {M : ℕ} {h : GL (Fin 2) ℚ_[q]} (hhK : h ∈ Kq q) (hh : h ∈ Omega q M) :
    h⁻¹ ∈ Omega q M := by
  obtain ⟨b, m, hb, hm, rfl⟩ := hh
  have hbK : b ∈ Kq q := by
    have : b * m * m⁻¹ ∈ Kq q := (Kq q).mul_mem hhK ((Kq q).inv_mem (KM_le_Kq q M hm))
    rwa [mul_inv_cancel_right] at this
  refine ⟨b⁻¹, b * m⁻¹ * b⁻¹, isUpper_inv q hb, conj_mem_KM q hbK ((KM q M).inv_mem hm), ?_⟩
  rw [mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem inv_mul_mem_Omega {M : ℕ} {g k₁ k₂ : GL (Fin 2) ℚ_[q]} (hk₁ : k₁ ∈ Kq q) (hk₂ : k₂ ∈ Kq q)
    (h₁ : g * k₁ ∈ Omega q M) (h₂ : g * k₂ ∈ Omega q M) : k₁⁻¹ * k₂ ∈ Omega q M := by
  obtain ⟨b₁, m₁, hb₁, hm₁, e₁⟩ := h₁
  obtain ⟨b₂, m₂, hb₂, hm₂, e₂⟩ := h₂

  have hk : k₁⁻¹ * k₂ = m₁⁻¹ * (b₁⁻¹ * b₂) * m₂ := by
    have e₁' : k₁ = g⁻¹ * (b₁ * m₁) := by rw [← e₁, inv_mul_cancel_left]
    have e₂' : k₂ = g⁻¹ * (b₂ * m₂) := by rw [← e₂, inv_mul_cancel_left]
    rw [e₁', e₂']
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hbK : b₁⁻¹ * b₂ ∈ Kq q := by
    have : m₁ * (k₁⁻¹ * k₂) * m₂⁻¹ ∈ Kq q :=
      (Kq q).mul_mem ((Kq q).mul_mem (KM_le_Kq q M hm₁) ((Kq q).mul_mem ((Kq q).inv_mem hk₁) hk₂))
        ((Kq q).inv_mem (KM_le_Kq q M hm₂))
    rw [hk] at this
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using this
  rw [hk]
  refine ⟨b₁⁻¹ * b₂, (b₁⁻¹ * b₂)⁻¹ * m₁⁻¹ * (b₁⁻¹ * b₂) * m₂,
    isUpper_mul q (isUpper_inv q hb₁) hb₂,
    (KM q M).mul_mem (conj_mem_KM' q hbK ((KM q M).inv_mem hm₁)) hm₂, ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left]

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

private def HM (M : ℕ) : Subgroup ↥(Kq q) where
  carrier := {k | (k : GL (Fin 2) ℚ_[q]) ∈ Omega q M}
  one_mem' := one_mem_Omega q M
  mul_mem' := fun {_ b} ha hb => mul_mem_Omega_of_mem_Kq q ha b.2 hb
  inv_mem' := fun {a} ha => inv_mem_Omega_of_mem_Kq q a.2 ha

private theorem mem_HM_iff {M : ℕ} (k : ↥(Kq q)) : k ∈ HM q M ↔ (k : GL (Fin 2) ℚ_[q]) ∈ Omega q M := Iff.rfl

private theorem KM_subgroupOf_le_HM (M : ℕ) : (KM q M).subgroupOf (Kq q) ≤ HM q M := by
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  rw [mem_HM_iff]
  have := mem_Omega_of_isUpper_of_mem q (isUpper_one q) hk
  rwa [one_mul] at this

private scoped instance finiteIndex_HM (M : ℕ) : (HM q M).FiniteIndex :=
  haveI := SteinbergGenFI.finiteIndex_gl2CongruenceSubgroup_subgroupOf_padicK1 q M 0
  Subgroup.finiteIndex_of_le (KM_subgroupOf_le_HM q M)

private scoped instance fintypeQuot (M : ℕ) : Fintype (↥(Kq q) ⧸ HM q M) := Subgroup.fintypeQuotientOfFiniteIndex

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

private theorem decomp {M : ℕ} (F : GL (Fin 2) ℚ_[q] → ℂ) (hB : ∀ b g, IsUpper q b → F (b * g) = F g)
    (hK : ∀ m ∈ KM q M, ∀ g, F (g * m) = F g) (g : GL (Fin 2) ℚ_[q]) :
    F g = ∑ c : ↥(Kq q) ⧸ HM q M,
      F ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹ * E q M (g * ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])) := by
  classical
  obtain ⟨b, k, hk, hb, hgbk⟩ := LocalGL2.iwasawa_decomposition ℤ_[q] ℚ_[q] g
  have hkK : k ∈ Kq q := (mem_Kq_iff q k).mpr hk
  have hbU : IsUpper q b := hb
  set kK : ↥(Kq q) := ⟨k, hkK⟩ with hkKdef
  set c₀ : ↥(Kq q) ⧸ HM q M := QuotientGroup.mk kK⁻¹ with hc₀
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (HM q M) kK⁻¹

  have hmain : g * ((c₀.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q]) ∈ Omega q M := by
    rw [hc₀, hh, hgbk]
    change b * k * (k⁻¹ * (h : ↥(Kq q))) ∈ Omega q M
    rw [mul_assoc, mul_inv_cancel_left, upper_mul_mem_Omega_iff q hbU]
    exact h.2
  rw [Finset.sum_eq_single c₀]
  ·
    rw [E_of_mem q hmain, mul_one]
    obtain ⟨b', m', hb', hm', e⟩ := hmain
    set r := ((c₀.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q]) with hr
    have hrK : r ∈ Kq q := (c₀.out : ↥(Kq q)).2
    have hg' : g = b' * (r⁻¹ * (r * m' * r⁻¹)) := by
      rw [show b' * (r⁻¹ * (r * m' * r⁻¹)) = b' * m' * r⁻¹ by group, ← e, mul_inv_cancel_right]
    rw [hg', hB _ _ hb', hK _ (conj_mem_KM q hrK hm')]
  · intro c _ hc
    have hnot : g * ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q]) ∉ Omega q M := by
      intro hin
      apply hc
      have hmem : ((c₀.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹ * ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])
          ∈ Omega q M :=
        inv_mul_mem_Omega q (c₀.out : ↥(Kq q)).2 (c.out : ↥(Kq q)).2 hmain hin
      have hmem' : (c₀.out : ↥(Kq q))⁻¹ * (c.out : ↥(Kq q)) ∈ HM q M := hmem
      have := QuotientGroup.eq.mpr hmem'
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      exact this.symm
    rw [E_of_not_mem q hnot, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ c₀) h

private theorem mem_of_E_mem {M : ℕ} (S : Submodule ℂ (GL (Fin 2) ℚ_[q] → ℂ)) (hS : ∀ h, ∀ F ∈ S, rt q h F ∈ S)
    (hE : E q M ∈ S) (F : GL (Fin 2) ℚ_[q] → ℂ) (hB : ∀ b g, IsUpper q b → F (b * g) = F g)
    (hK : ∀ m ∈ KM q M, ∀ g, F (g * m) = F g) : F ∈ S := by
  classical
  have hF : F = ∑ c : ↥(Kq q) ⧸ HM q M,
      F ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹ • rt q ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q]) (E q M) := by
    funext g
    rw [decomp q F hB hK g, Finset.sum_apply]
    simp [rt]
  rw [hF]
  exact S.sum_mem fun c _ => S.smul_mem _ (hS _ _ hE)

private theorem exists_max_modulus {M : ℕ} (F : GL (Fin 2) ℚ_[q] → ℂ) (hB : ∀ b g, IsUpper q b → F (b * g) = F g)
    (hK : ∀ m ∈ KM q M, ∀ g, F (g * m) = F g) :
    ∃ k₀ ∈ Kq q, ∀ g, ‖F g‖ ≤ ‖F k₀‖ := by
  classical
  obtain ⟨c₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (↥(Kq q) ⧸ HM q M))
    (fun c => ‖F ((c.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹‖) Finset.univ_nonempty
  refine ⟨((c₀.out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹, (Kq q).inv_mem (c₀.out : ↥(Kq q)).2, fun g => ?_⟩

  obtain ⟨b, k, hk, hb, hgbk⟩ := LocalGL2.iwasawa_decomposition ℤ_[q] ℚ_[q] g
  have hkK : k ∈ Kq q := (mem_Kq_iff q k).mpr hk
  have hbU : IsUpper q b := hb
  set kK : ↥(Kq q) := ⟨k, hkK⟩ with hkKdef
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (HM q M) kK⁻¹
  have hval : F g = F (((QuotientGroup.mk kK⁻¹ : ↥(Kq q) ⧸ HM q M).out : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹ := by
    rw [hh, hgbk, hB _ _ hbU]
    change F k = F (k⁻¹ * (h : ↥(Kq q)) : GL (Fin 2) ℚ_[q])⁻¹
    obtain ⟨b', m', hb', hm', e⟩ := (h.2 : ((h : ↥(Kq q)) : GL (Fin 2) ℚ_[q]) ∈ Omega q M)
    have hhK : (b' * m' : GL (Fin 2) ℚ_[q]) ∈ Kq q := by rw [← e]; exact (h : ↥(Kq q)).2
    have hb'K : b' ∈ Kq q := by
      have : b' * m' * m'⁻¹ ∈ Kq q := (Kq q).mul_mem hhK ((Kq q).inv_mem (KM_le_Kq q M hm'))
      rwa [mul_inv_cancel_right] at this
    rw [mul_inv_rev, inv_inv, e, mul_inv_rev]

    have hconj : b'⁻¹ * k * ((b'⁻¹ * k)⁻¹ * m'⁻¹ * (b'⁻¹ * k)) = m'⁻¹ * b'⁻¹ * k := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [← hconj, hK _ (conj_mem_KM' q ((Kq q).mul_mem ((Kq q).inv_mem hb'K) hkK) ((KM q M).inv_mem hm')),
      hB _ _ (isUpper_inv q hb')]
  rw [hval]
  exact hmax _ (Finset.mem_univ _)

private theorem exists_level_of_borelInvariant {f : GL (Fin 2) ℚ_[q] → ℂ} (hlc : IsLocallyConstant f)
    (hB : ∀ b g, IsUpper q b → f (b * g) = f g) : ∃ M, ∀ m ∈ KM q M, ∀ g, f (g * m) = f g := by
  classical

  have hloc : ∀ k : GL (Fin 2) ℚ_[q], ∃ M, ∀ m ∈ KM q M, f (k * m) = f k := by
    intro k
    have hopen : IsOpen ((fun h : GL (Fin 2) ℚ_[q] => k * h) ⁻¹' (f ⁻¹' {f k})) :=
      (hlc.isOpen_fiber (f k)).preimage (continuous_const.mul continuous_id)
    have hmem : (fun h : GL (Fin 2) ℚ_[q] => k * h) ⁻¹' (f ⁻¹' {f k}) ∈ 𝓝 (1 : GL (Fin 2) ℚ_[q]) :=
      hopen.mem_nhds (by simp)
    obtain ⟨M, hM⟩ := FLT.SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one q hmem
    exact ⟨M, fun m hm => hM hm⟩
  choose Mk hMk using hloc

  have hKc : IsCompact ((Kq q : Subgroup (GL (Fin 2) ℚ_[q])) : Set (GL (Fin 2) ℚ_[q])) := by
    rw [show Kq q = LocalGL2.integralSubgroup ℤ_[q] ℚ_[q] from padicK1_zero_eq_integralSubgroup q]
    exact FLT.SpectralSide.isCompact_coe_integralSubgroup_padic q
  let U : GL (Fin 2) ℚ_[q] → Set (GL (Fin 2) ℚ_[q]) := fun k => (fun h => k * h) '' (KM q (Mk k) : Set _)
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (isOpenMap_mul_left k) _ (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q (Mk k))
  have hcover : ((Kq q : Subgroup (GL (Fin 2) ℚ_[q])) : Set (GL (Fin 2) ℚ_[q])) ⊆ ⋃ k, U k := by
    intro k _
    exact Set.mem_iUnion.mpr ⟨k, ⟨1, (KM q (Mk k)).one_mem, mul_one k⟩⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover U hUo hcover
  refine ⟨t.sup Mk, fun m hm g => ?_⟩

  obtain ⟨b, k, hk, hb, rfl⟩ := LocalGL2.iwasawa_decomposition ℤ_[q] ℚ_[q] g
  have hkK : k ∈ Kq q := (mem_Kq_iff q k).mpr hk
  rw [mul_assoc, hB _ _ hb, hB _ _ hb]

  obtain ⟨kᵢ, hkᵢt, hkU⟩ : ∃ kᵢ ∈ t, k ∈ U kᵢ := by
    have := ht hkK
    simpa only [Set.mem_iUnion, exists_prop] using this
  obtain ⟨h, hh, rfl⟩ := hkU
  have hle : Mk kᵢ ≤ t.sup Mk := Finset.le_sup hkᵢt
  have hm' : m ∈ KM q (Mk kᵢ) := FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q hle hm
  rw [mul_assoc, hMk kᵢ (h * m) ((KM q (Mk kᵢ)).mul_mem hh hm'), hMk kᵢ h hh]

end SteinbergGen
p2m_reactivate "P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable.SteinbergGen"

namespace SteinbergGen

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

open Classical in

private def EZ (N : ℤ) : GL (Fin 2) ℚ_[q] → ℂ := fun g => if g ∈ OmegaZ q N then 1 else 0

private theorem mem_OmegaZ_iff (N : ℤ) (g : GL (Fin 2) ℚ_[q]) :
    g ∈ OmegaZ q N ↔ ‖lo q g‖ ≤ (q : ℝ) ^ (-N) * ‖lr q g‖ := Iff.rfl

private theorem Omega_eq_OmegaZ {M : ℕ} (hM : 1 ≤ M) : Omega q M = OmegaZ q (M : ℤ) := by
  ext g
  rw [mem_Omega_iff_norm q hM, mem_OmegaZ_iff]

private theorem E_eq_EZ {M : ℕ} (hM : 1 ≤ M) : E q M = EZ q (M : ℤ) := by
  funext g
  unfold E EZ
  exact ind_congr (by rw [Omega_eq_OmegaZ q hM])

private theorem norm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[q])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := q) (n : ℤ)
  simpa using this

end SteinbergGen
p2m_reactivate "P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable.SteinbergGen"

namespace SteinbergGen

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

private scoped instance neZero_pow (L : ℕ) : NeZero (q ^ L) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩

private def avgN (L : ℕ) (Φ : GL (Fin 2) ℚ_[q] → ℂ) : GL (Fin 2) ℚ_[q] → ℂ :=
  ∑ y : ZMod (q ^ L), rt q (upperN q ((y.val : ℕ) : ℚ_[q])) Φ

private def avgT (L : ℕ) (Φ : GL (Fin 2) ℚ_[q] → ℂ) : GL (Fin 2) ℚ_[q] → ℂ :=
  ∑ x : (ZMod (q ^ L))ˣ, rt q (diagE q (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q])) Φ

private theorem norm_unitVal_eq_one {L : ℕ} (hL : 1 ≤ L) (x : (ZMod (q ^ L))ˣ) :
    ‖(((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  have hcop := ZMod.val_coe_unit_coprime x
  exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self q (by omega)) hcop).symm

private theorem unitVal_ne_zero {L : ℕ} (hL : 1 ≤ L) (x : (ZMod (q ^ L))ˣ) :
    (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q]) ≠ 0 := by
  intro h
  have := norm_unitVal_eq_one q hL x
  rw [h, norm_zero] at this
  exact zero_ne_one this

private theorem level_rt {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ m ∈ KM q L, rt q m Φ = Φ) {h : GL (Fin 2) ℚ_[q]}
    (hh : h ∈ Kq q) : ∀ m ∈ KM q L, rt q m (rt q h Φ) = rt q h Φ := by
  intro m hm
  rw [← rt_mul, show m * h = h * (h⁻¹ * m * h) by group, rt_mul, hΦ _ (conj_mem_KM' q hh hm)]

private theorem upper_rt {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ b g, IsUpper q b → Φ (b * g) = Φ g)
    (h : GL (Fin 2) ℚ_[q]) :
    ∀ b g, IsUpper q b → rt q h Φ (b * g) = rt q h Φ g := by
  intro b g hb
  rw [rt_apply, rt_apply, mul_assoc, hΦ _ _ hb]

private theorem avgN_mem {L : ℕ} (S : Submodule ℂ (GL (Fin 2) ℚ_[q] → ℂ)) (hS : ∀ h, ∀ F ∈ S, rt q h F ∈ S)
    {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : Φ ∈ S) : avgN q L Φ ∈ S :=
  S.sum_mem fun _ _ => hS _ _ hΦ

private theorem avgT_mem {L : ℕ} (S : Submodule ℂ (GL (Fin 2) ℚ_[q] → ℂ)) (hS : ∀ h, ∀ F ∈ S, rt q h F ∈ S)
    {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : Φ ∈ S) : avgT q L Φ ∈ S :=
  S.sum_mem fun _ _ => hS _ _ hΦ

private theorem avgN_upper {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ b g, IsUpper q b → Φ (b * g) = Φ g) :
    ∀ b g, IsUpper q b → avgN q L Φ (b * g) = avgN q L Φ g := by
  intro b g hb
  simp only [avgN, Finset.sum_apply]
  exact Finset.sum_congr rfl fun y _ => upper_rt q hΦ _ b g hb

private theorem avgT_upper {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ b g, IsUpper q b → Φ (b * g) = Φ g) :
    ∀ b g, IsUpper q b → avgT q L Φ (b * g) = avgT q L Φ g := by
  intro b g hb
  simp only [avgT, Finset.sum_apply]
  exact Finset.sum_congr rfl fun y _ => upper_rt q hΦ _ b g hb

private theorem avgN_level {L : ℕ} {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ m ∈ KM q L, rt q m Φ = Φ) :
    ∀ m ∈ KM q L, rt q m (avgN q L Φ) = avgN q L Φ := by
  intro m hm
  unfold avgN
  rw [rt_sum]
  exact Finset.sum_congr rfl fun y _ => level_rt q hΦ (upperN_mem_Kq q (norm_natCast_le_one q _)) m hm

private theorem avgT_level {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ m ∈ KM q L, rt q m Φ = Φ) :
    ∀ m ∈ KM q L, rt q m (avgT q L Φ) = avgT q L Φ := by
  intro m hm
  unfold avgT
  rw [rt_sum]
  exact Finset.sum_congr rfl fun x _ => level_rt q hΦ (diagE_mem_Kq q (norm_unitVal_eq_one q hL x)) m hm

private theorem norm_sub_le_of_toZModPow_eq {L : ℕ} {a b : ℤ_[q]}
    (h : PadicInt.toZModPow L a = PadicInt.toZModPow L b) :
    ‖((a : ℚ_[q]) - b)‖ ≤ (q : ℝ) ^ (-(L : ℤ)) := by
  have hmem : a - b ∈ RingHom.ker (PadicInt.toZModPow L) := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZModPow] at hmem
  have := (PadicInt.norm_le_pow_iff_mem_span_pow (a - b) L).mpr hmem
  simp at this ⊢
  exact this

private theorem avgN_transl {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ m ∈ KM q L, rt q m Φ = Φ) :
    ∀ x : ℚ_[q], ‖x‖ ≤ 1 → rt q (upperN q x) (avgN q L Φ) = avgN q L Φ := by
  intro x hx
  unfold avgN
  rw [rt_sum]
  set xz : ℤ_[q] := ⟨x, hx⟩ with hxz
  set xb : ZMod (q ^ L) := PadicInt.toZModPow L xz with hxb

  have hterm : ∀ y : ZMod (q ^ L), rt q (upperN q x) (rt q (upperN q ((y.val : ℕ) : ℚ_[q])) Φ)
      = rt q (upperN q ((((xb + y).val : ℕ)) : ℚ_[q])) Φ := by
    intro y
    rw [← rt_mul, upperN_mul]
    set δ : ℚ_[q] := x + ((y.val : ℕ) : ℚ_[q]) - (((xb + y).val : ℕ) : ℚ_[q]) with hδ
    have hδn : ‖δ‖ ≤ (q : ℝ) ^ (-(L : ℤ)) := by
      have h := norm_sub_le_of_toZModPow_eq q (L := L) (a := xz + ((y.val : ℕ) : ℤ_[q]))
        (b := (((xb + y).val : ℕ) : ℤ_[q])) (by
          rw [map_add, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
      rw [PadicInt.coe_add, PadicInt.coe_natCast, PadicInt.coe_natCast] at h
      rw [hδ]
      exact h
    have hsplit : upperN q (x + ((y.val : ℕ) : ℚ_[q])) = upperN q ((((xb + y).val : ℕ)) : ℚ_[q]) * upperN q δ := by
      rw [upperN_mul]; congr 1; rw [hδ]; ring
    rw [hsplit, rt_mul, hΦ _ (upperN_mem_KM q hL hδn)]
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  exact Equiv.sum_comp (Equiv.addLeft xb) (fun y => rt q (upperN q ((y.val : ℕ) : ℚ_[q])) Φ)

private theorem avgT_torus {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ} (hΦ : ∀ m ∈ KM q L, rt q m Φ = Φ) :
    ∀ a : ℚ_[q], ‖a‖ = 1 → rt q (diagE q a) (avgT q L Φ) = avgT q L Φ := by
  intro a ha
  have ha1 : ‖a‖ ≤ 1 := ha.le
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  unfold avgT
  rw [rt_sum]
  set az : ℤ_[q] := ⟨a, ha1⟩ with haz
  have hazu : IsUnit az := PadicInt.isUnit_iff.mpr (by simpa [haz] using ha)
  set ab : (ZMod (q ^ L))ˣ := Units.map (PadicInt.toZModPow L).toMonoidHom hazu.unit with hab
  have hterm : ∀ x : (ZMod (q ^ L))ˣ,
      rt q (diagE q a) (rt q (diagE q (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q])) Φ)
        = rt q (diagE q ((((ab * x : (ZMod (q ^ L))ˣ) : ZMod (q ^ L)).val : ℕ) : ℚ_[q])) Φ := by
    intro x
    have hv0 := unitVal_ne_zero q hL x
    have hw0 := unitVal_ne_zero q hL (ab * x)
    rw [← rt_mul, diagE_mul q ha0 hv0]
    set v : ℚ_[q] := (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q]) with hv
    set w : ℚ_[q] := ((((ab * x : (ZMod (q ^ L))ˣ) : ZMod (q ^ L)).val : ℕ) : ℚ_[q]) with hw
    set ε : ℚ_[q] := a * v / w with hε
    have hε1 : ‖ε - 1‖ ≤ (q : ℝ) ^ (-(L : ℤ)) := by
      have hnum : ‖a * v - w‖ ≤ (q : ℝ) ^ (-(L : ℤ)) := by
        have h := norm_sub_le_of_toZModPow_eq q (L := L) (a := az * (((x : ZMod (q ^ L)).val : ℕ) : ℤ_[q]))
          (b := ((((ab * x : (ZMod (q ^ L))ˣ) : ZMod (q ^ L)).val : ℕ) : ℤ_[q])) (by
            rw [map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_mul,
              hab, Units.coe_map]
            rfl)
        rw [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_natCast] at h
        rw [hv, hw]
        exact h
      have hw1 : ‖w‖ = 1 := norm_unitVal_eq_one q hL (ab * x)
      rw [hε, show a * v / w - 1 = (a * v - w) / w by field_simp, norm_div, hw1, div_one]
      exact hnum
    have hεne : ε ≠ 0 := by
      intro h
      have := norm_eq_one_of_norm_sub_one_le q hL hε1
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hsplit : diagE q (a * v) = diagE q w * diagE q ε := by
      rw [diagE_mul q hw0 hεne]; congr 1; rw [hε]; field_simp
    rw [hsplit, rt_mul, hΦ _ (diagE_mem_KM q hL hε1)]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  exact Equiv.sum_comp (Equiv.mulLeft ab) (fun x => rt q (diagE q (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q])) Φ)

private theorem avgT_transl {L : ℕ} (hL : 1 ≤ L) {Φ : GL (Fin 2) ℚ_[q] → ℂ}
    (hΦ : ∀ x : ℚ_[q], ‖x‖ ≤ 1 → rt q (upperN q x) Φ = Φ) :
    ∀ x : ℚ_[q], ‖x‖ ≤ 1 → rt q (upperN q x) (avgT q L Φ) = avgT q L Φ := by
  intro x hx
  unfold avgT
  rw [rt_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hv0 := unitVal_ne_zero q hL y
  rw [← rt_mul, upperN_mul_diagE q x hv0, rt_mul, hΦ]
  rw [norm_div, norm_unitVal_eq_one q hL y, div_one]
  exact hx

private theorem eq_of_sum_eq_card_mul {ι : Type*} (s : Finset ι) (v : ι → ℂ) (V : ℂ) (hle : ∀ i ∈ s, ‖v i‖ ≤ ‖V‖)
    (hsum : ∑ i ∈ s, v i = s.card * V) : ∀ i ∈ s, v i = V := by
  by_cases hV : V = 0
  · intro i hi
    have := hle i hi
    rw [hV, norm_zero] at this
    rw [hV]
    exact norm_le_zero_iff.mp this
  · have hVn : 0 < ‖V‖ := norm_pos_iff.mpr hV
    set u : ι → ℂ := fun i => v i / V with hu
    have hule : ∀ i ∈ s, ‖u i‖ ≤ 1 := fun i hi => by
      rw [hu, norm_div, div_le_one hVn]; exact hle i hi
    have husum : ∑ i ∈ s, u i = s.card := by
      simp only [hu]
      rw [← Finset.sum_div, hsum, mul_div_assoc, div_self hV, mul_one]
    have hre : ∑ i ∈ s, (1 - (u i).re) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Complex.re_sum, husum]
      simp
    have hnonneg : ∀ i ∈ s, 0 ≤ 1 - (u i).re := fun i hi => by
      have := le_trans (Complex.re_le_norm (u i)) (hule i hi)
      linarith
    have hre1 : ∀ i ∈ s, (u i).re = 1 := fun i hi => by
      have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hre i hi
      linarith
    intro i hi
    have him : (u i).im = 0 := by
      have h1 := hule i hi
      have h2 : ‖u i‖ ^ 2 = (u i).re * (u i).re + (u i).im * (u i).im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      rw [hre1 i hi] at h2
      have h3 : ‖u i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
      have h4 : (u i).im * (u i).im ≤ 0 := by rw [h2] at h3; linarith
      exact mul_self_eq_zero.mp (le_antisymm h4 (mul_self_nonneg _))
    have hui : u i = 1 := Complex.ext (by rw [hre1 i hi]; rfl) (by rw [him]; rfl)
    have : v i / V = 1 := hui
    rwa [div_eq_one_iff_eq hV] at this

private theorem const_of_avg_const {L : ℕ} (hL : 1 ≤ L) {Φ₀ : GL (Fin 2) ℚ_[q] → ℂ}
    (hB : ∀ b g, IsUpper q b → Φ₀ (b * g) = Φ₀ g) (hmax : ∀ g, ‖Φ₀ g‖ ≤ ‖Φ₀ 1‖)
    (hconst : ∀ g, avgT q L (avgN q L Φ₀) g = avgT q L (avgN q L Φ₀) 1) : ∀ g, Φ₀ g = Φ₀ 1 := by
  intro g
  have hexp : ∀ g', avgT q L (avgN q L Φ₀) g' = ∑ x : (ZMod (q ^ L))ˣ, ∑ y : ZMod (q ^ L),
      Φ₀ (g' * diagE q (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q]) * upperN q ((y.val : ℕ) : ℚ_[q])) := by
    intro g'
    simp only [avgT, avgN, Finset.sum_apply, rt_apply]
  have h1 : avgT q L (avgN q L Φ₀) 1 = ∑ x : (ZMod (q ^ L))ˣ, ∑ y : ZMod (q ^ L), Φ₀ 1 := by
    rw [hexp]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [one_mul, ← mul_one (diagE q _ * upperN q _)]
    exact hB _ _ (isUpper_mul q (isUpper_diagE q _) (isUpper_upperN q _))
  have hg := hconst g
  rw [hexp, h1] at hg

  have hout := eq_of_sum_eq_card_mul (Finset.univ : Finset (ZMod (q ^ L))ˣ)
    (fun x => ∑ y : ZMod (q ^ L),
      Φ₀ (g * diagE q (((x : ZMod (q ^ L)).val : ℕ) : ℚ_[q]) * upperN q ((y.val : ℕ) : ℚ_[q])))
    (∑ y : ZMod (q ^ L), Φ₀ 1) (fun x _ => by
      beta_reduce
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
      refine le_trans (norm_sum_le _ _) ?_
      rw [show (Fintype.card (ZMod (q ^ L)) : ℝ) * ‖Φ₀ 1‖ = ∑ y : ZMod (q ^ L), ‖Φ₀ 1‖ by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
      exact Finset.sum_le_sum fun y _ => hmax _) (by
      rw [hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  have hx1 := hout 1 (Finset.mem_univ _)
  beta_reduce at hx1

  have hin := eq_of_sum_eq_card_mul (Finset.univ : Finset (ZMod (q ^ L)))
    (fun y =>
      Φ₀ (g * diagE q ((((1 : (ZMod (q ^ L))ˣ) : ZMod (q ^ L)).val : ℕ) : ℚ_[q]) * upperN q ((y.val : ℕ) : ℚ_[q])))
    (Φ₀ 1) (fun y _ => hmax _) (by beta_reduce; rw [hx1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  have hy0 := hin 0 (Finset.mem_univ _)
  beta_reduce at hy0
  haveI : Fact (1 < q ^ L) := ⟨Nat.one_lt_pow (by omega) (Fact.out : q.Prime).one_lt⟩
  simp only [Units.val_one, ZMod.val_one, Nat.cast_one, ZMod.val_zero, Nat.cast_zero, diagE_one, upperN_zero,
    mul_one] at hy0
  exact hy0

section Heart

variable (S : Submodule ℂ (GL (Fin 2) ℚ_[q] → ℂ)) (hS : ∀ h, ∀ F ∈ S, rt q h F ∈ S)
include hS

private theorem exists_radial_nonconst {L : ℕ} (hL : 1 ≤ L) (F : GL (Fin 2) ℚ_[q] → ℂ) (hFS : F ∈ S)
    (hB : ∀ b g, IsUpper q b → F (b * g) = F g) (hK : ∀ m ∈ KM q L, ∀ g, F (g * m) = F g) (hnc : ∃ g, F g ≠ F 1) :
    ∃ Φ ∈ S, IsRadial q L Φ ∧ ∃ g, Φ g ≠ Φ 1 := by
  classical
  obtain ⟨k₀, hk₀, hmax⟩ := exists_max_modulus q F hB hK
  set Φ₀ := rt q k₀ F with hΦ₀
  have hΦ₀S : Φ₀ ∈ S := hS _ _ hFS
  have hB₀ : ∀ b g, IsUpper q b → Φ₀ (b * g) = Φ₀ g := upper_rt q hB k₀
  have hKF : ∀ m ∈ KM q L, rt q m F = F := fun m hm => funext fun g => hK m hm g
  have hK₀ : ∀ m ∈ KM q L, rt q m Φ₀ = Φ₀ := level_rt q hKF hk₀
  have hmax₀ : ∀ g, ‖Φ₀ g‖ ≤ ‖Φ₀ 1‖ := fun g => by simp only [hΦ₀, rt_apply, one_mul]; exact hmax _
  have hnc₀ : ¬ (∀ g, Φ₀ g = Φ₀ 1) := by
    intro hc
    obtain ⟨g, hg⟩ := hnc
    apply hg
    have e1 := hc (g * k₀⁻¹)
    have e2 := hc (k₀⁻¹)
    simp only [hΦ₀, rt_apply, inv_mul_cancel_right, one_mul, inv_mul_cancel] at e1 e2
    rw [e1, e2]
  refine ⟨avgT q L (avgN q L Φ₀), avgT_mem q S hS (avgN_mem q S hS hΦ₀S),
    ⟨avgT_upper q (avgN_upper q hB₀), avgT_transl q hL (avgN_transl q hL hK₀), avgT_torus q hL (avgN_level q hK₀),
      avgT_level q hL (avgN_level q hK₀)⟩, ?_⟩
  by_contra hno
  push Not at hno
  exact hnc₀ (const_of_avg_const q hL hB₀ hmax₀ hno)

end Heart
p2m_reactivate "P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable.SteinbergGen"

end SteinbergGen
p2m_reactivate "P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable.SteinbergGen"

end
p2m_reactivate "P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable.SteinbergGen"

open SteinbergGen in

theorem solution (p : ℕ) [Fact p.Prime] (S : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ))
    (hS : ∀ (h : GL (Fin 2) ℚ_[p]), ∀ F ∈ S, (fun g => F (g * h)) ∈ S)
    (F₀ : GL (Fin 2) ℚ_[p] → ℂ) (hF₀S : F₀ ∈ S) (hF₀lc : IsLocallyConstant F₀)
    (hF₀B : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → F₀ (b * g) = F₀ g)
    (hF₀nc : ∃ g : GL (Fin 2) ℚ_[p], F₀ g ≠ F₀ 1)
    (F : GL (Fin 2) ℚ_[p] → ℂ) (hFlc : IsLocallyConstant F)
    (hFB : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → F (b * g) = F g) :
    F ∈ S := by
  obtain ⟨L₀, hL₀⟩ := exists_level_of_borelInvariant p hF₀lc hF₀B
  obtain ⟨L, hLF⟩ := exists_level_of_borelInvariant p hFlc hFB
  have hK₀ : ∀ m ∈ KM p (max L₀ 1), ∀ g, F₀ (g * m) = F₀ g := fun m hm g =>
    hL₀ m (FLT.SmoothVectors.gl2CongruenceSubgroup_antitone p (le_max_left _ _) hm) g
  obtain ⟨Φ, hΦS, hΦ, hΦnc⟩ := exists_radial_nonconst p S hS (le_max_right L₀ 1) F₀ hF₀S hF₀B hK₀ hF₀nc
  have hT : ∀ a : ℚ_[p]ˣ, ‖(a : ℚ_[p])‖ = 1 →
      (fun g => Φ (g * LocalNewvector.borelElem p a 1 0)) = Φ := by
    intro a ha
    have h := hΦ.torus (a : ℚ_[p]) ha
    rw [diagE_of_ne_zero p a.ne_zero, Units.mk0_val] at h
    exact h
  have hcell : ∀ M : ℕ, 2 ≤ M → E p M ∈ S := by
    intro M hM
    have hind :=
      LocalNewvector.indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable p S hS Φ hΦS
        hΦ.upper (le_max_right L₀ 1) hΦ.level hΦ.transl hT hΦnc M hM
    have hEq : Set.indicator {g : GL (Fin 2) ℚ_[p] | ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖
        ≤ (p : ℝ) ^ (-(M : ℤ)) * ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖} (1 : GL (Fin 2) ℚ_[p] → ℂ)
          = EZ p (M : ℤ) := by
      funext g
      rw [Set.indicator_apply, Pi.one_apply]
      unfold EZ
      exact ind_congr Iff.rfl
    rw [E_eq_EZ p (by omega), ← hEq]
    exact hind
  exact mem_of_E_mem p S hS (hcell (max L 2) (le_max_right _ _)) F hFB
    (fun m hm g => hLF m (FLT.SmoothVectors.gl2CongruenceSubgroup_antitone p (le_max_left _ _) hm) g)

end S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable
end P2MW
export P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable (solution)
