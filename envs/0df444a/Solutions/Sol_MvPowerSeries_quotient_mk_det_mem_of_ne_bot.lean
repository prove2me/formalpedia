-- Prove2me | solution 1 for MvPowerSeries.quotient_mk_det_mem_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b9a04ac2-efb3-5633-aef6-41d6e2353279

import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.Algebra.Polynomial.Div
import Theorems.Thm_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_quotient_mk_det_mem_of_ne_bot

universe u

open MvPowerSeries

namespace TateK

section Support

variable {σ : Type*} {R : Type*} [CommRing R]

def upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if N ≤ m i then coeff m h else 0

theorem coeff_upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (upperPart i N h) = if N ≤ m i then coeff m h else 0 := rfl

theorem X_pow_dvd_upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) :
    (X i : MvPowerSeries σ R) ^ N ∣ upperPart i N h :=
  X_pow_dvd_iff.mpr fun m hm => by rw [coeff_upperPart, if_neg (not_le.mpr hm)]

theorem coeff_sub_upperPart_of_le {i : σ} {N : ℕ} (h : MvPowerSeries σ R) {m : σ →₀ ℕ} (hm : N ≤ m i) :
    coeff m (h - upperPart i N h) = 0 := by
  rw [map_sub, coeff_upperPart, if_pos hm, sub_self]

theorem coeff_sub_upperPart_of_lt {i : σ} {N : ℕ} (h : MvPowerSeries σ R) {m : σ →₀ ℕ} (hm : m i < N) :
    coeff m (h - upperPart i N h) = coeff m h := by
  rw [map_sub, coeff_upperPart, if_neg (not_le.mpr hm), sub_zero]

theorem coeff_eq_zero_of_mem_span (T : Set σ) (N : σ → ℕ) {h : MvPowerSeries σ R}
    (hmem : h ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' T))
    (m : σ →₀ ℕ) (hm : ∀ i ∈ T, m i < N i) : coeff m h = 0 := by
  classical
  induction hmem using Submodule.span_induction generalizing m with
  | mem p hp =>
    obtain ⟨i, hi, rfl⟩ := hp
    rw [coeff_X_pow, if_neg]
    intro hmi
    have := hm i hi
    rw [hmi, Finsupp.single_eq_same] at this
    exact lt_irrefl _ this
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp m hm, hq m hm, add_zero]
  | smul a p _ hp =>
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun uv huv => ?_
    rw [hp uv.2 (fun i hi => lt_of_le_of_lt ?_ (hm i hi)), mul_zero]
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    rw [← this, Finsupp.add_apply]
    exact Nat.le_add_left _ _

theorem mem_span_X_pow_iff (S : Finset σ) (N : σ → ℕ) (h : MvPowerSeries σ R) :
    h ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑S : Set σ)) ↔
      ∀ m : σ →₀ ℕ, (∀ i ∈ S, m i < N i) → coeff m h = 0 := by
  classical
  refine ⟨fun hmem m hm => coeff_eq_zero_of_mem_span _ N hmem m (fun i hi => hm i hi), ?_⟩
  induction S using Finset.induction_on generalizing h with
  | empty =>
    intro H
    have : h = 0 := MvPowerSeries.ext fun m => by rw [H m (fun i hi => absurd hi (Finset.notMem_empty i)), map_zero]
    rw [this]
    exact Submodule.zero_mem _
  | insert i S hi IH =>
    intro H
    have h1 : upperPart i (N i) h ∈
        Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑(insert i S) : Set σ)) := by
      obtain ⟨q, hq⟩ := X_pow_dvd_upperPart i (N i) h
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, Finset.mem_insert_self i S, rfl⟩)
    have h2 : h - upperPart i (N i) h ∈
        Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑(insert i S) : Set σ)) := by
      refine Ideal.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_insert i S))) (IH _ ?_)
      intro m hm
      by_cases hle : N i ≤ m i
      · exact coeff_sub_upperPart_of_le h hle
      · rw [coeff_sub_upperPart_of_lt h (not_le.mp hle)]
        exact H m fun j hj => by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact not_le.mp hle
          · exact hm j hj
    have := add_mem h2 h1
    rwa [sub_add_cancel] at this

theorem mem_span_range_X_iff [Fintype σ] (h : MvPowerSeries σ R) :
    h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ↔ constantCoeff h = 0 := by
  have hset : Set.range (X : σ → MvPowerSeries σ R) =
      (fun i => (X i : MvPowerSeries σ R) ^ (fun _ => 1) i) '' (↑(Finset.univ : Finset σ) : Set σ) := by
    rw [Finset.coe_univ, Set.image_univ]
    exact congrArg Set.range (funext fun i => (pow_one _).symm)
  rw [hset, mem_span_X_pow_iff, ← coeff_zero_eq_constantCoeff_apply]
  constructor
  · intro H; exact H 0 fun i _ => Nat.one_pos
  · intro H m hm
    have : m = 0 := Finsupp.ext fun i => Nat.lt_one_iff.mp (hm i (Finset.mem_univ i))
    rw [this, H]

end Support

section Regular

variable {R : Type*} [CommRing R]

theorem isSMulRegular_quotient_ideal (I : Ideal R) (r : R) (H : ∀ h, r * h ∈ I → h ∈ I) :
    IsSMulRegular (R ⧸ (I • ⊤ : Submodule R R)) r := by
  have hI : (I • ⊤ : Submodule R R) = I := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  change r • Submodule.Quotient.mk a = r • Submodule.Quotient.mk b at hab
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← smul_sub, hI,
    smul_eq_mul] at hab
  rw [Submodule.Quotient.eq, hI]
  exact H _ hab

variable {n : ℕ}

theorem setOf_mem_take_ofFn {α : Type*} (y : Fin n → α) (j : ℕ) :
    {r | r ∈ (List.ofFn y).take j} = y '' {i : Fin n | (i : ℕ) < j} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image, List.mem_iff_getElem, List.length_take, List.length_ofFn,
    List.getElem_take, List.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, (lt_min_iff.mp hi).2⟩, (lt_min_iff.mp hi).1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, lt_min_iff.mpr ⟨hi, i.2⟩, rfl⟩

theorem isWeaklyRegular_X_pow (N : Fin n → ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) R)
      (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R) ^ N i) := by
  classical
  refine (RingTheory.Sequence.isWeaklyRegular_iff_Fin _ _).mpr fun j => ?_
  rw [Fin.getElem_fin, List.getElem_ofFn]
  apply isSMulRegular_quotient_ideal
  intro h hmem

  have hS : {r | r ∈ (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R) ^ N i).take j} =
      (fun i => (X i : MvPowerSeries (Fin n) R) ^ (N i)) ''
        (↑(Finset.univ.filter fun i : Fin n => (i : ℕ) < j) : Set (Fin n)) := by
    rw [setOf_mem_take_ofFn, Finset.coe_filter]
    simp
  dsimp only [Ideal.ofList] at hmem ⊢
  rw [hS, mem_span_X_pow_iff (N := fun i => N i)] at hmem ⊢
  intro m hm
  have hjn : (j : ℕ) < n := by simpa using j.2
  have key := hmem (Finsupp.single (⟨j, hjn⟩ : Fin n) (N ⟨j, hjn⟩) + m) fun i hi => by
    have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne, zero_add]
    · exact hm i hi
    · intro h'; rw [h'] at hij; exact lt_irrefl (j : ℕ) hij
  rwa [X_pow_eq, coeff_add_monomial_mul, one_mul] at key

end Regular

section Powers

variable {k : Type u} [Field k] {σ : Type*}

theorem exists_X_pow_mem (I : Ideal (MvPowerSeries σ k)) [Module.Finite k (MvPowerSeries σ k ⧸ I)] (i : σ) :
    ∃ N : ℕ, (X i : MvPowerSeries σ k) ^ N ∈ I := by
  obtain ⟨p, pmonic, hp⟩ : IsIntegral k (Ideal.Quotient.mk I (X i)) := Algebra.IsIntegral.isIntegral _

  have hpI : Polynomial.aeval (X i : MvPowerSeries σ k) p ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k, ← Polynomial.aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    exact hp

  obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial k) ^ p.natTrailingDegree ∣ p :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 ≠ 0 := by
    have := Polynomial.coeff_X_pow_mul q p.natTrailingDegree 0
    rw [zero_add, ← hq] at this
    rw [← this]
    exact mt Polynomial.trailingCoeff_eq_zero.mp pmonic.ne_zero

  have hunit : IsUnit (Polynomial.aeval (X i : MvPowerSeries σ k) q) := by
    rw [isUnit_iff_constantCoeff, Polynomial.aeval_def, Polynomial.hom_eval₂, constantCoeff_X,
      Polynomial.eval₂_at_zero]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← c_eq_algebraMap, constantCoeff_C]
    exact isUnit_iff_ne_zero.mpr hq0
  refine ⟨p.natTrailingDegree, ?_⟩
  rw [hq, map_mul, map_pow, Polynomial.aeval_X] at hpI
  obtain ⟨u, hu⟩ := hunit
  rw [← hu] at hpI
  have := I.mul_mem_right (↑u⁻¹ : MvPowerSeries σ k) hpI
  rwa [mul_assoc, Units.mul_inv, mul_one] at this

end Powers

section Socle

variable {B : Type*} [CommRing B]

theorem exists_mul_ne_zero_and_forall_mul_eq_zero (𝔪 : Ideal B) (h𝔪 : IsNilpotent 𝔪) {y : B} (hy : y ≠ 0) :
    ∃ w : B, w * y ≠ 0 ∧ ∀ v ∈ 𝔪, v * (w * y) = 0 := by
  classical

  let Q : ℕ → Prop := fun t => ∀ w ∈ 𝔪 ^ t, w * y = 0
  obtain ⟨R, hR⟩ := h𝔪
  have hex : ∃ t, Q t := ⟨R, fun w hw => by rw [hR] at hw; rw [(Submodule.mem_bot B).mp hw, zero_mul]⟩
  have h0 : ¬Q 0 := fun H => hy (by simpa using H 1 (by rw [pow_zero, Ideal.one_eq_top]; trivial))
  have hpos : 0 < Nat.find hex := Nat.pos_of_ne_zero fun h => h0 (h ▸ Nat.find_spec hex)
  have hnot : ¬Q (Nat.find hex - 1) := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
  simp only [Q, not_forall, exists_prop] at hnot
  obtain ⟨w, hw, hwy⟩ := hnot
  refine ⟨w, hwy, fun v hv => ?_⟩
  rw [← mul_assoc]
  apply Nat.find_spec hex
  have : Nat.find hex = Nat.find hex - 1 + 1 := (Nat.sub_add_cancel hpos).symm
  rw [this, pow_succ']
  exact Ideal.mul_mem_mul hv hw

end Socle

section Main

variable {k : Type u} [Field k] {n : ℕ}

theorem span_range_X_ne_top : Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) k)) ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPowerSeries (Fin n) k) ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) k)) := by
    rw [h]; trivial
  rw [mem_span_range_X_iff, map_one] at h1
  exact one_ne_zero h1

theorem main (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ J := by
  classical

  choose N hN using fun i : Fin n => exists_X_pow_mem (Ideal.span (Set.range f)) i

  obtain ⟨hcol₁, hcol₂⟩ := Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular
    (fun j : Fin n => (X j : MvPowerSeries (Fin n) k)) f g hf ⟨fun i => X i ^ N i, isWeaklyRegular_X_pow N, hN⟩
  have hXtop : Ideal.span (Set.range fun j : Fin n => (X j : MvPowerSeries (Fin n) k)) ≠ ⊤ :=
    span_range_X_ne_top

  have hdet : g.det ∉ Ideal.span (Set.range f) := fun hmem => hXtop <| by
    rw [← hcol₂]
    exact (Submodule.colon_eq_top_iff_subset _).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  refine ⟨fun h0 => hdet (Ideal.Quotient.eq_zero_iff_mem.mp h0), fun J hJ => ?_⟩

  set d := Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det with hd
  set 𝔪 : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    Ideal.span (Set.range fun j : Fin n => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) with h𝔪

  have hxd : ∀ j : Fin n, Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j) * d = 0 := fun j => by
    rw [hd, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_colon_span_singleton, hcol₂]
    exact Ideal.subset_span ⟨j, rfl⟩
  have h𝔪d : ∀ v ∈ 𝔪, v * d = 0 := by
    have hle : 𝔪 ≤ (⊥ : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))).colon {d} :=
      Ideal.span_le.mpr fun v ⟨j, hj⟩ => by
        rw [← hj, SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul, hxd j]
        exact Submodule.zero_mem _
    intro v hv
    have := hle hv
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] at this

  have h𝔪nil : IsNilpotent 𝔪 := by
    have hfg : 𝔪.FG := ⟨Finset.univ.image fun j : Fin n => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j), by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    refine (Ideal.FG.isNilpotent_iff_le_nilradical hfg).mpr (Ideal.span_le.mpr ?_)
    rintro v ⟨j, rfl⟩
    exact mem_nilradical.mpr ⟨N j, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hN j⟩

  obtain ⟨y, hyJ, hy0⟩ := (Submodule.ne_bot_iff J).mp hJ
  obtain ⟨w, hz0, hz𝔪⟩ := exists_mul_ne_zero_and_forall_mul_eq_zero 𝔪 h𝔪nil hy0
  have hzJ : w * y ∈ J := J.mul_mem_left w hyJ

  obtain ⟨zt, hzt⟩ := Ideal.Quotient.mk_surjective (w * y)
  have hzt_col : zt ∈ (Ideal.span (Set.range f)).colon
      (Ideal.span (Set.range fun j : Fin n => (X j : MvPowerSeries (Fin n) k))) := by
    rw [Ideal.colon_span, Submodule.mem_colon]
    rintro _ ⟨j, rfl⟩
    rw [smul_eq_mul, mul_comm, ← Ideal.Quotient.eq_zero_iff_mem, map_mul, hzt]
    exact hz𝔪 _ (Ideal.subset_span ⟨j, rfl⟩)
  rw [hcol₁] at hzt_col
  obtain ⟨a, ha, bd, hbd, habd⟩ := Submodule.mem_sup.mp hzt_col
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hbd

  have hz : w * y = Ideal.Quotient.mk (Ideal.span (Set.range f)) b * d := by
    rw [← hzt, ← habd, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul]
  have hb𝔪 : Ideal.Quotient.mk (Ideal.span (Set.range f)) (b - C (constantCoeff b)) ∈ 𝔪 := by
    have hmem : b - C (constantCoeff b) ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) k)) := by
      rw [mem_span_range_X_iff, map_sub, constantCoeff_C, sub_self]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span (Set.range f))) hmem
    rwa [Ideal.map_span, ← Set.range_comp] at this
  have hz' : w * y = Ideal.Quotient.mk (Ideal.span (Set.range f)) (C (constantCoeff b)) * d := by
    have hsplit : Ideal.Quotient.mk (Ideal.span (Set.range f)) b =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) (C (constantCoeff b)) +
          Ideal.Quotient.mk (Ideal.span (Set.range f)) (b - C (constantCoeff b)) := by
      rw [← map_add, add_sub_cancel]
    rw [hz, hsplit, add_mul, h𝔪d _ hb𝔪, add_zero]

  have hb0 : constantCoeff b ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, zero_mul] at hz'
    exact hz0 hz'
  have : d = Ideal.Quotient.mk (Ideal.span (Set.range f)) (C (constantCoeff b)⁻¹) * (w * y) := by
    rw [hz', ← mul_assoc, ← map_mul, ← map_mul (C : k →+* MvPowerSeries (Fin n) k), inv_mul_cancel₀ hb0,
      map_one, map_one, one_mul]
  rw [this]
  exact J.mul_mem_left _ hzJ

end Main

end TateK

theorem solution
    {k : Type u} [Field k] {n : ℕ} (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ J := by
  exact TateK.main g f hf

end S_MvPowerSeries_quotient_mk_det_mem_of_ne_bot
end P2MW
export P2MW.S_MvPowerSeries_quotient_mk_det_mem_of_ne_bot (solution)
