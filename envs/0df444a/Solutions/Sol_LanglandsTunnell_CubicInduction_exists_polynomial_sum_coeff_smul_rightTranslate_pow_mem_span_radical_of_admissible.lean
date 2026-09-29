-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6ee36e23-0fa0-5771-8584-b02f18cab1cb

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

import Mathlib.Topology.Algebra.OpenSubgroup
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

noncomputable section

namespace SlJ2

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

def gl3RightStabilizer (W : LocalGL3 v → ℂ) : Subgroup (LocalGL3 v) where
  carrier := {g | gl3AmbientRightTranslate (R := ℂ) g W = W}
  one_mem' := by
    change gl3AmbientRightTranslate (R := ℂ) (1 : LocalGL3 v) W = W
    funext h
    simp only [gl3AmbientRightTranslate_apply, mul_one]
  mul_mem' := by
    intro a b ha hb
    change gl3AmbientRightTranslate (R := ℂ) a W = W at ha
    change gl3AmbientRightTranslate (R := ℂ) b W = W at hb
    change gl3AmbientRightTranslate (R := ℂ) (a * b) W = W
    funext h
    have hb' := congrFun hb (h * a)
    have ha' := congrFun ha h
    simp only [gl3AmbientRightTranslate_apply] at hb' ha' ⊢
    rw [← mul_assoc, hb', ha']
  inv_mem' := by
    intro a ha
    change gl3AmbientRightTranslate (R := ℂ) a W = W at ha
    change gl3AmbientRightTranslate (R := ℂ) a⁻¹ W = W
    funext h
    have ha' := congrFun ha (h * a⁻¹)
    simp only [gl3AmbientRightTranslate_apply] at ha' ⊢
    rw [← ha', inv_mul_cancel_right]

theorem mem_gl3RightStabilizer_iff {W : LocalGL3 v → ℂ} {g : LocalGL3 v} :
    g ∈ gl3RightStabilizer v W ↔ ∀ h : LocalGL3 v, W (h * g) = W h := by
  change gl3AmbientRightTranslate (R := ℂ) g W = W ↔ _
  constructor
  · intro hg h
    have := congrFun hg h
    simpa only [gl3AmbientRightTranslate_apply] using this
  · intro hg
    funext h
    simp only [gl3AmbientRightTranslate_apply, hg h]

theorem isOpen_gl3RightStabilizer_of_exists {W : LocalGL3 v → ℂ}
    (hW : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) :
    IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  obtain ⟨Uv, hUv, hfix⟩ := hW
  refine Subgroup.isOpen_mono (fun k hk => ?_) hUv
  exact (mem_gl3RightStabilizer_iff v).2 fun h => hfix k hk h

theorem isOpen_gl3RightStabilizer_translate {W : LocalGL3 v → ℂ}
    (hW : IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v))) (a : LocalGL3 v) :
    IsOpen ((gl3RightStabilizer v (gl3AmbientRightTranslate (R := ℂ) a W) : Subgroup (LocalGL3 v)) :
      Set (LocalGL3 v)) := by

  have hconj : IsOpen (((gl3RightStabilizer v W).map (MulAut.conj a).toMonoidHom : Subgroup (LocalGL3 v)) :
      Set (LocalGL3 v)) := by
    have : (((gl3RightStabilizer v W).map (MulAut.conj a).toMonoidHom : Subgroup (LocalGL3 v)) :
        Set (LocalGL3 v)) = (Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹) ''
          ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Homeomorph.trans_apply,
        Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this]
    exact (Homeomorph.isOpenMap _) _ hW
  refine Subgroup.isOpen_mono ?_ hconj
  rintro _ ⟨s, hs, rfl⟩
  refine (mem_gl3RightStabilizer_iff v).2 fun h => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, gl3AmbientRightTranslate_apply]
  have hs' := (mem_gl3RightStabilizer_iff v).1 hs (h * a)
  calc W (h * (a * s * a⁻¹) * a) = W (h * a * s) := by group
    _ = W (h * a) := hs'

theorem isOpen_gl3RightStabilizer_of_mem_gl3CyclicSubspace {W₀ : LocalGL3 v → ℂ}
    (h₀ : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₀) :
    IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hbase := isOpen_gl3RightStabilizer_of_exists v h₀
  refine Submodule.span_induction
    (p := fun f _ => IsOpen ((gl3RightStabilizer v f : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)))
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨a, rfl⟩
    exact isOpen_gl3RightStabilizer_translate v hbase a
  · refine Subgroup.isOpen_mono (H₁ := ⊤) (fun g _ => ?_) ?_
    · exact (mem_gl3RightStabilizer_iff v).2 fun _ => rfl
    · simp
  · intro f₁ f₂ _ _ h₁ h₂
    refine Subgroup.isOpen_mono (H₁ := gl3RightStabilizer v f₁ ⊓ gl3RightStabilizer v f₂) (fun g hg => ?_) ?_
    · obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
      refine (mem_gl3RightStabilizer_iff v).2 fun h => ?_
      simp only [Pi.add_apply, (mem_gl3RightStabilizer_iff v).1 hg₁ h, (mem_gl3RightStabilizer_iff v).1 hg₂ h]
    · simpa only [Subgroup.coe_inf] using h₁.inter h₂
  · intro c f _ hf
    refine Subgroup.isOpen_mono (H₁ := gl3RightStabilizer v f) (fun g hg => ?_) hf
    refine (mem_gl3RightStabilizer_iff v).2 fun h => ?_
    simp only [Pi.smul_apply, (mem_gl3RightStabilizer_iff v).1 hg h]

noncomputable def gl3FiniteAverage (C : Subgroup (LocalGL3 v)) (W : LocalGL3 v → ℂ) :
    LocalGL3 v → ℂ :=
  ∑ᶠ x : C ⧸ (gl3RightStabilizer v W).subgroupOf C, gl3AmbientRightTranslate (R := ℂ) (x.out : LocalGL3 v) W

theorem finite_quotient_of_isCompact_of_isOpen {C : Subgroup (LocalGL3 v)}
    (hC : IsCompact (C : Set (LocalGL3 v))) {W : LocalGL3 v → ℂ}
    (hW : IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v))) :
    Finite (C ⧸ (gl3RightStabilizer v W).subgroupOf C) := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen C _ hW)

theorem gl3FiniteAverage_apply {C : Subgroup (LocalGL3 v)} (hC : IsCompact (C : Set (LocalGL3 v)))
    {W : LocalGL3 v → ℂ} (hW : IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)))
    (g : LocalGL3 v) :
    gl3FiniteAverage v C W g =
      ∑ᶠ x : C ⧸ (gl3RightStabilizer v W).subgroupOf C, W (g * (x.out : LocalGL3 v)) := by
  haveI := finite_quotient_of_isCompact_of_isOpen v hC hW
  unfold gl3FiniteAverage
  rw [finsum_apply]
  · simp only [gl3AmbientRightTranslate_apply]
  · exact Set.toFinite _

theorem gl3FiniteAverage_mem {C : Subgroup (LocalGL3 v)} (hC : IsCompact (C : Set (LocalGL3 v)))
    {W₀ W : LocalGL3 v → ℂ}
    (hW : IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)))
    (hmem : W ∈ gl3CyclicSubspace W₀) : gl3FiniteAverage v C W ∈ gl3CyclicSubspace W₀ := by
  haveI := finite_quotient_of_isCompact_of_isOpen v hC hW
  cases nonempty_fintype (C ⧸ (gl3RightStabilizer v W).subgroupOf C)
  unfold gl3FiniteAverage
  rw [finsum_eq_sum_of_fintype]
  exact Submodule.sum_mem _ fun x _ => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W₀ _ hmem

theorem gl3FiniteAverage_mul_mem {C : Subgroup (LocalGL3 v)} (hC : IsCompact (C : Set (LocalGL3 v)))
    {W : LocalGL3 v → ℂ} (hW : IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)))
    {k : LocalGL3 v} (hk : k ∈ C) (g : LocalGL3 v) :
    gl3FiniteAverage v C W (g * k) = gl3FiniteAverage v C W g := by
  haveI := finite_quotient_of_isCompact_of_isOpen v hC hW
  rw [gl3FiniteAverage_apply v hC hW, gl3FiniteAverage_apply v hC hW]
  set H : Subgroup C := (gl3RightStabilizer v W).subgroupOf C
  set kC : C := ⟨k, hk⟩

  have hterm : ∀ x : C ⧸ H, W (g * k * (x.out : LocalGL3 v)) = W (g * ((kC • x).out : LocalGL3 v)) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (kC * x.out)
    have hmk : (QuotientGroup.mk (kC * x.out) : C ⧸ H) = kC • x := by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk H kC x.out, QuotientGroup.out_eq']
    rw [hmk] at hh
    rw [hh]
    have hfix : ((h : C) : LocalGL3 v) ∈ gl3RightStabilizer v W := Subgroup.mem_subgroupOf.1 h.2
    have := (mem_gl3RightStabilizer_iff v).1 hfix (g * k * (x.out : LocalGL3 v))
    simp only [Subgroup.coe_mul] at this ⊢
    rw [← this]
    congr 1
    simp only [kC, mul_assoc]
  simp_rw [hterm]
  exact finsum_comp_equiv (f := fun y : C ⧸ H => W (g * (y.out : LocalGL3 v))) (MulAction.toPerm (β := C ⧸ H) kC)

theorem card_pos_of_finite {C : Subgroup (LocalGL3 v)} (hC : IsCompact (C : Set (LocalGL3 v)))
    {W : LocalGL3 v → ℂ} (hW : IsOpen ((gl3RightStabilizer v W : Subgroup (LocalGL3 v)) : Set (LocalGL3 v))) :
    0 < Nat.card (C ⧸ (gl3RightStabilizer v W).subgroupOf C) := by
  haveI := finite_quotient_of_isCompact_of_isOpen v hC hW
  haveI : Nonempty (C ⧸ (gl3RightStabilizer v W).subgroupOf C) := ⟨QuotientGroup.mk 1⟩
  exact Nat.card_pos

abbrev Fv : Type := v.adicCompletion ℚ

abbrev mat (g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (Fv v) := (g : Matrix (Fin 3) (Fin 3) (Fv v))

theorem mat_mul (g k : LocalGL3 v) (i j : Fin 3) :
    mat v (g * k) i j = mat v g i 0 * mat v k 0 j + mat v g i 1 * mat v k 1 j + mat v g i 2 * mat v k 2 j := by
  simp [mat, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

def CongOne (e : WithZero (Multiplicative ℤ)) (M : Matrix (Fin 3) (Fin 3) (Fv v)) : Prop :=
  ∀ i j, Valued.v (M i j - (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j) ≤ e

theorem congOne_one (e : WithZero (Multiplicative ℤ)) : CongOne v e 1 := by
  intro i j; simp

theorem valued_sum3_le {a b c : Fv v} {e : WithZero (Multiplicative ℤ)} (ha : Valued.v a ≤ e) (hb : Valued.v b ≤ e)
    (hc : Valued.v c ≤ e) : Valued.v (a + b + c) ≤ e :=
  (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le ha hb)) hc)

theorem congOne_mul {e : WithZero (Multiplicative ℤ)} (he : e ≤ 1) {M N : Matrix (Fin 3) (Fin 3) (Fv v)}
    (hM : CongOne v e M) (hN : CongOne v e N) : CongOne v e (M * N) := by
  intro i j
  have key : (M * N) i j - (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j =
      ((M - 1) * (N - 1)) i j + (M - 1) i j + (N - 1) i j := by
    have : M * N - 1 = (M - 1) * (N - 1) + (M - 1) + (N - 1) := by noncomm_ring
    have h := congrFun (congrFun this i) j
    simpa only [Matrix.sub_apply, Matrix.add_apply] using h
  rw [key]
  refine valued_sum3_le v ?_ (hM i j) (hN i j)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  have h1 : ∀ l, Valued.v ((M - 1) i l * (N - 1) l j) ≤ e := fun l => by
    rw [map_mul, Matrix.sub_apply, Matrix.sub_apply]
    calc Valued.v (M i l - (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i l) * Valued.v (N l j - (1 : Matrix _ _ _) l j)
        ≤ e * 1 := mul_le_mul' (hM i l) ((hN l j).trans he)
      _ = e := mul_one e
  exact valued_sum3_le v (h1 0) (h1 1) (h1 2)

def Kc (e : WithZero (Multiplicative ℤ)) (he : e ≤ 1) : Subgroup (LocalGL3 v) where
  carrier := {k | CongOne v e (mat v k) ∧ CongOne v e (mat v k⁻¹)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show CongOne v e (mat v 1); rw [show mat v 1 = 1 from Units.val_one]; exact congOne_one v e
    · show CongOne v e (mat v 1⁻¹); rw [inv_one, show mat v 1 = 1 from Units.val_one]; exact congOne_one v e
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · show CongOne v e (mat v (a * b)); rw [show mat v (a * b) = mat v a * mat v b from Units.val_mul _ _]
      exact congOne_mul v he ha hb
    · show CongOne v e (mat v (a * b)⁻¹)
      rw [_root_.mul_inv_rev, show mat v (b⁻¹ * a⁻¹) = mat v b⁻¹ * mat v a⁻¹ from Units.val_mul _ _]
      exact congOne_mul v he hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by show CongOne v e (mat v a⁻¹⁻¹); rw [inv_inv]; exact ha⟩

theorem mem_Kc_iff {e : WithZero (Multiplicative ℤ)} {he : e ≤ 1} {k : LocalGL3 v} :
    k ∈ Kc v e he ↔ CongOne v e (mat v k) ∧ CongOne v e (mat v k⁻¹) := Iff.rfl

end SlJ2

namespace SlJ2

open Filter Topology

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

theorem restrict_ne_zero {y : Fv v} (hy : y ≠ 0) :
    (Valued.v.restrict y : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation (Fv v) (WithZero (Multiplicative ℤ))))) ≠ 0 := by
  rw [Ne, Valuation.restrict_eq_zero_iff]
  exact (Valuation.ne_zero_iff _).2 hy

theorem isOpen_ball {y : Fv v} (hy : y ≠ 0) (c : Fv v) :
    IsOpen {x : Fv v | Valued.v (x - c) ≤ Valued.v y} := by
  have h := (Valued.isOpen_closedBall (R := Fv v) (restrict_ne_zero v hy)).preimage (continuous_sub_right c)
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← not_lt, Valuation.restrict_lt_iff]

theorem isClosed_ball (y : Fv v) (c : Fv v) :
    IsClosed {x : Fv v | Valued.v (x - c) ≤ Valued.v y} := by
  have h := (Valued.isClosed_closedBall (Fv v) (Valued.v.restrict y)).preimage (continuous_sub_right c)
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← not_lt, Valuation.restrict_lt_iff]

theorem coe_Kc (e : WithZero (Multiplicative ℤ)) (he : e ≤ 1) :
    ((Kc v e he : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      ⋂ i : Fin 3, ⋂ j : Fin 3, ({k : LocalGL3 v | Valued.v (mat v k i j - (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j) ≤ e} ∩
        {k : LocalGL3 v | Valued.v (mat v k⁻¹ i j - (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j) ≤ e}) := by
  ext k
  simp only [SetLike.mem_coe, mem_Kc_iff, CongOne, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun h i j => ⟨h.1 i j, h.2 i j⟩, fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩⟩

theorem isOpen_Kc {y : Fv v} (hy : y ≠ 0) (he : Valued.v y ≤ 1) :
    IsOpen ((Kc v (Valued.v y) he : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [coe_Kc]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_ball v hy _).preimage (Units.continuous_val.matrix_elem i j)
  · exact (isOpen_ball v hy _).preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem isClosed_Kc (y : Fv v) (he : Valued.v y ≤ 1) :
    IsClosed ((Kc v (Valued.v y) he : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  rw [coe_Kc]
  refine isClosed_iInter fun i => isClosed_iInter fun j => IsClosed.inter ?_ ?_
  · exact (isClosed_ball v y _).preimage (Units.continuous_val.matrix_elem i j)
  · exact (isClosed_ball v y _).preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem valued_le_one_of_congOne {e : WithZero (Multiplicative ℤ)} (he : e ≤ 1) {M : Matrix (Fin 3) (Fin 3) (Fv v)}
    (hM : CongOne v e M) (i j : Fin 3) : Valued.v (M i j) ≤ 1 := by
  have h1 : Valued.v ((1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j) ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have : M i j = (M i j - (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j) + (1 : Matrix (Fin 3) (Fin 3) (Fv v)) i j := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le ((hM i j).trans he) h1)

theorem Kc_le_max (e : WithZero (Multiplicative ℤ)) (he : e ≤ 1) :
    (Kc v e he : Subgroup (LocalGL3 v)) ≤ localMaximalCompact3 (NumberField.RingOfIntegers ℚ) ℚ v := by
  intro k hk
  exact ⟨fun i j => valued_le_one_of_congOne v he hk.1 i j, fun i j => valued_le_one_of_congOne v he hk.2 i j⟩

theorem isCompact_Kc (y : Fv v) (he : Valued.v y ≤ 1) :
    IsCompact ((Kc v (Valued.v y) he : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) :=
  (isCompact_localMaximalCompact3 v).of_isClosed_subset (isClosed_Kc v y he) (Kc_le_max v _ he)

variable {π : Fv v} (hπv : Valued.v π = WithZero.exp (-1 : ℤ))
include hπv

theorem v_pow (n : ℕ) : Valued.v (π ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, hπv]
  have hne : (WithZero.exp (-1 : ℤ)) ^ n ≠ 0 := pow_ne_zero n WithZero.exp_ne_zero
  rw [← WithZero.exp_log hne, WithZero.log_pow, WithZero.log_exp]
  congr 1
  simp

omit hπv in
theorem π_ne_zero (hπv : Valued.v π = WithZero.exp (-1 : ℤ)) : π ≠ 0 := fun h => by
  rw [h, map_zero] at hπv; exact WithZero.exp_ne_zero hπv.symm

theorem v_pow_le_one (n : ℕ) : Valued.v (π ^ n) ≤ 1 := by
  rw [v_pow v hπv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem v_pow_lt_one {n : ℕ} (hn : 1 ≤ n) : Valued.v (π ^ n) < 1 := by
  rw [v_pow v hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem tendsto_of_valued_sub_le {f : ℕ → Fv v} {a : Fv v}
    (hf : ∀ n : ℕ, Valued.v (f n - a) ≤ Valued.v (π ^ (n + 1))) : Tendsto f atTop (𝓝 a) := by
  rw [tendsto_nhds]
  intro s hs has
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (hs.mem_nhds has)
  have hE : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 :=
    (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).2 γ.ne_zero
  rw [mem_atTop_sets]
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val)).toNat, fun n hn => hγ ?_⟩
  show Valued.v.restrict (f n - a) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  calc Valued.v (f n - a) ≤ Valued.v (π ^ (n + 1)) := hf n
    _ = WithZero.exp (-((n + 1 : ℕ) : ℤ)) := v_pow v hπv (n + 1)
    _ < WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val)) :=
        WithZero.exp_lt_exp.2 (by push_cast; omega)
    _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.val := WithZero.exp_log hE

theorem exists_Kc_le {S : Subgroup (LocalGL3 v)} (hS : IsOpen (S : Set (LocalGL3 v))) :
    ∃ n : ℕ, (Kc v (Valued.v (π ^ (n + 1))) (v_pow_le_one v hπv (n + 1)) : Subgroup (LocalGL3 v)) ≤ S := by
  by_contra h
  push Not at h
  have h' : ∀ n : ℕ, ∃ k : LocalGL3 v, k ∈ Kc v (Valued.v (π ^ (n + 1))) (v_pow_le_one v hπv (n + 1)) ∧ k ∉ S := by
    intro n
    obtain ⟨k, hk, hkS⟩ := Set.not_subset.1 (h n)
    exact ⟨k, hk, hkS⟩
  choose k hk using h'
  have ht : Tendsto k atTop (𝓝 (1 : LocalGL3 v)) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply, Units.val_one, inv_one]
    refine Filter.Tendsto.prodMk_nhds ?_ ?_
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact tendsto_of_valued_sub_le v hπv fun n => (hk n).1.1 i j
    · refine (MulOpposite.continuous_op.tendsto _).comp ?_
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact tendsto_of_valued_sub_le v hπv fun n => (hk n).1.2 i j
  obtain ⟨n, hn⟩ := (ht.eventually_mem (hS.mem_nhds S.one_mem)).exists
  exact (hk n).2 hn

end SlJ2

namespace SlJ2

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

def dU (α β : (Fv v)ˣ) : GL (Fin 2) (Fv v) :=
  ⟨!![(α : Fv v), 0; 0, (β : Fv v)], !![((α⁻¹ : (Fv v)ˣ) : Fv v), 0; 0, ((β⁻¹ : (Fv v)ˣ) : Fv v)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_dU (α β : (Fv v)ˣ) :
    ((dU v α β : GL (Fin 2) (Fv v)) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![(α : Fv v), 0; 0, (β : Fv v)] := rfl

theorem dU_inv (α β : (Fv v)ˣ) : (dU v α β)⁻¹ = dU v α⁻¹ β⁻¹ := Units.ext rfl

theorem dU_mul (α β γ δ : (Fv v)ˣ) : dU v α β * dU v γ δ = dU v (α * γ) (β * δ) := by
  apply Units.ext
  rw [Units.val_mul, coe_dU, coe_dU, coe_dU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def sHom : (Fv v)ˣ →* GL (Fin 2) (Fv v) where
  toFun α := dU v α α
  map_one' := by
    apply Units.ext
    rw [coe_dU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' α γ := (dU_mul v α α γ γ).symm

def dHom1 : (Fv v)ˣ →* GL (Fin 2) (Fv v) where
  toFun α := dU v α 1
  map_one' := by
    apply Units.ext
    rw [coe_dU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' α γ := by rw [dU_mul, mul_one]

theorem scalarPi_pow (π : Fv v) (hπ : π ≠ 0) (n : ℕ) :
    scalarPi π hπ ^ n = dU v (Units.mk0 π hπ ^ n) (Units.mk0 π hπ ^ n) := by
  have h : scalarPi π hπ = sHom v (Units.mk0 π hπ) := by
    apply Units.ext
    show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) (Fv v)) =
      ((dU v (Units.mk0 π hπ) (Units.mk0 π hπ) : GL (Fin 2) (Fv v)) : Matrix _ _ _)
    rw [coe_dU]; rfl
  rw [h, ← map_pow]; rfl

theorem diagUnitGL2_pow (π : Fv v) (hπ : π ≠ 0) (n : ℕ) :
    diagUnitGL2 (Units.mk0 π hπ) ^ n = dU v (Units.mk0 π hπ ^ n) 1 := by
  have h : diagUnitGL2 (Units.mk0 π hπ) = dHom1 v (Units.mk0 π hπ) := by
    apply Units.ext
    show (!![((Units.mk0 π hπ : (Fv v)ˣ) : Fv v), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (Fv v)) =
      (dU v (Units.mk0 π hπ) 1).val
    rw [coe_dU, Units.val_one]
  rw [h, ← map_pow]; rfl

theorem inv_conj (a b : (Fv v)ˣ) (p : LocalGL3 v) :
    (iotaGL (dU v a⁻¹ b⁻¹) * p * iotaGL (dU v a b))⁻¹ = iotaGL (dU v a⁻¹ b⁻¹) * p⁻¹ * iotaGL (dU v a b) := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, dU_inv, dU_inv, inv_inv, inv_inv, mul_assoc]

theorem mat_conj12 (α : (Fv v)ˣ) (p : LocalGL3 v) :
    mat v (iotaGL (dU v α⁻¹ 1) * p * iotaGL (dU v α 1)) =
      !![mat v p 0 0, ((α⁻¹ : (Fv v)ˣ) : Fv v) * mat v p 0 1, ((α⁻¹ : (Fv v)ˣ) : Fv v) * mat v p 0 2;
         (α : Fv v) * mat v p 1 0, mat v p 1 1, mat v p 1 2;
         (α : Fv v) * mat v p 2 0, mat v p 2 1, mat v p 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat_mul, coe_iotaGL, coe_dU, embedMat2]
  all_goals first | exact mul_comm _ _ | (rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero α), one_mul])

theorem mat_conj21 (α : (Fv v)ˣ) (p : LocalGL3 v) :
    mat v (iotaGL (dU v α⁻¹ α⁻¹) * p * iotaGL (dU v α α)) =
      !![mat v p 0 0, mat v p 0 1, ((α⁻¹ : (Fv v)ˣ) : Fv v) * mat v p 0 2;
         mat v p 1 0, mat v p 1 1, ((α⁻¹ : (Fv v)ˣ) : Fv v) * mat v p 1 2;
         (α : Fv v) * mat v p 2 0, (α : Fv v) * mat v p 2 1, mat v p 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat_mul, coe_iotaGL, coe_dU, embedMat2]
  all_goals first | exact mul_comm _ _ | (rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero α), one_mul]) | trace_state

theorem v_diag_sub_one_le' {e : WithZero (Multiplicative ℤ)} {k : LocalGL3 v} (hk : CongOne v e (mat v k))
    (i : Fin 3) : Valued.v (mat v k i i - 1) ≤ e := by
  have h := hk i i
  rwa [Matrix.one_apply_eq] at h

theorem v_offdiag_le' {e : WithZero (Multiplicative ℤ)} {k : LocalGL3 v} (hk : CongOne v e (mat v k))
    {i j : Fin 3} (hij : i ≠ j) : Valued.v (mat v k i j) ≤ e := by
  have h := hk i j
  rwa [Matrix.one_apply_ne hij, sub_zero] at h

theorem congOne_conj12 {e : WithZero (Multiplicative ℤ)} {p : LocalGL3 v} (hp : CongOne v e (mat v p))
    (h01 : mat v p 0 1 = 0) (h02 : mat v p 0 2 = 0) {α : (Fv v)ˣ} (hα : Valued.v (α : Fv v) ≤ 1) :
    CongOne v e (mat v (iotaGL (dU v α⁻¹ 1) * p * iotaGL (dU v α 1))) := by
  have hd := v_diag_sub_one_le' v hp
  have ho := fun i j (h : i ≠ j) => v_offdiag_le' v hp h
  have hm : ∀ x : Fv v, Valued.v x ≤ e → Valued.v ((α : Fv v) * x) ≤ e := fun x hx => by
    rw [map_mul]; exact (mul_le_mul' hα hx).trans_eq (one_mul e)
  intro i j
  rw [mat_conj12]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, h01, h02, mul_zero]
  · simpa using hd 0
  · simp
  · simp
  · simpa using hm _ (ho 1 0 (by decide))
  · simpa using hd 1
  · simpa using ho 1 2 (by decide)
  · simpa using hm _ (ho 2 0 (by decide))
  · simpa using ho 2 1 (by decide)
  · simpa using hd 2

theorem congOne_conj21 {e : WithZero (Multiplicative ℤ)} {p : LocalGL3 v} (hp : CongOne v e (mat v p))
    (h02 : mat v p 0 2 = 0) (h12 : mat v p 1 2 = 0) {α : (Fv v)ˣ} (hα : Valued.v (α : Fv v) ≤ 1) :
    CongOne v e (mat v (iotaGL (dU v α⁻¹ α⁻¹) * p * iotaGL (dU v α α))) := by
  have hd := v_diag_sub_one_le' v hp
  have ho := fun i j (h : i ≠ j) => v_offdiag_le' v hp h
  have hm : ∀ x : Fv v, Valued.v x ≤ e → Valued.v ((α : Fv v) * x) ≤ e := fun x hx => by
    rw [map_mul]; exact (mul_le_mul' hα hx).trans_eq (one_mul e)
  intro i j
  rw [mat_conj21]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, h02, h12, mul_zero]
  · simpa using hd 0
  · simpa using ho 0 1 (by decide)
  · simp
  · simpa using ho 1 0 (by decide)
  · simpa using hd 1
  · simp
  · simpa using hm _ (ho 2 0 (by decide))
  · simpa using hm _ (ho 2 1 (by decide))
  · simpa using hd 2

theorem v_entry_le {e : WithZero (Multiplicative ℤ)} (he : e ≤ 1) {k : LocalGL3 v} (hk : CongOne v e (mat v k))
    (i j : Fin 3) : Valued.v (mat v k i j) ≤ 1 := valued_le_one_of_congOne v he hk i j

theorem v_offdiag_le {e : WithZero (Multiplicative ℤ)} {k : LocalGL3 v} (hk : CongOne v e (mat v k))
    {i j : Fin 3} (hij : i ≠ j) : Valued.v (mat v k i j) ≤ e := by
  have h := hk i j
  rwa [Matrix.one_apply_ne hij, sub_zero] at h

theorem ne_zero_of_v_sub_one_lt {x : Fv v} (h : Valued.v (x - 1) < 1) : x ≠ 0 := by
  intro hx
  rw [hx, zero_sub, Valuation.map_neg, Valuation.map_one] at h
  exact lt_irrefl _ h

theorem v_eq_one_of_v_sub_one_lt {x : Fv v} (h : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ h

theorem v_diag_sub_one_le {e : WithZero (Multiplicative ℤ)} {k : LocalGL3 v} (hk : CongOne v e (mat v k))
    (i : Fin 3) : Valued.v (mat v k i i - 1) ≤ e := by
  have h := hk i i
  rwa [Matrix.one_apply_eq] at h

theorem factor12 {e : WithZero (Multiplicative ℤ)} (he : e ≤ 1) (he1 : e < 1) {k : LocalGL3 v}
    (hk : k ∈ Kc v e he) :
    ∃ (w : Fin 2 → Fv v) (p : LocalGL3 v), k = radicalP12 w * p ∧ p ∈ Kc v e he ∧
      mat v p 0 1 = 0 ∧ mat v p 0 2 = 0 ∧ mat v p⁻¹ 0 1 = 0 ∧ mat v p⁻¹ 0 2 = 0 := by
  obtain ⟨hk1, hk2⟩ := hk

  set D : Fv v := mat v k 1 1 * mat v k 2 2 - mat v k 1 2 * mat v k 2 1 with hD
  have hD1 : Valued.v (D - 1) ≤ e := by
    have : D - 1 = (mat v k 1 1 - 1) * (mat v k 2 2 - 1) + (mat v k 1 1 - 1) + ((mat v k 2 2 - 1) +
        -(mat v k 1 2 * mat v k 2 1)) := by rw [hD]; ring
    rw [this]
    refine valued_sum3_le v ?_ (v_diag_sub_one_le v hk1 1) ((Valuation.map_add _ _ _).trans (max_le
      (v_diag_sub_one_le v hk1 2) ?_))
    · rw [map_mul]
      exact (mul_le_mul' (v_diag_sub_one_le v hk1 1) ((v_diag_sub_one_le v hk1 2).trans he)).trans_eq (mul_one e)
    · rw [Valuation.map_neg, map_mul]
      exact (mul_le_mul' (v_offdiag_le v hk1 (by decide)) (v_entry_le v he hk1 2 1)).trans_eq (mul_one e)
  have hDv : Valued.v D = 1 := v_eq_one_of_v_sub_one_lt v (hD1.trans_lt he1)
  have hDne : D ≠ 0 := ne_zero_of_v_sub_one_lt v (hD1.trans_lt he1)

  set x : Fv v := (mat v k 0 1 * mat v k 2 2 - mat v k 0 2 * mat v k 2 1) / D with hx
  set z : Fv v := (mat v k 0 2 * mat v k 1 1 - mat v k 0 1 * mat v k 1 2) / D with hz
  have hxv : Valued.v x ≤ e := by
    rw [hx, map_div₀, hDv, div_one]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul]
    · exact (mul_le_mul' (v_offdiag_le v hk1 (by decide)) (v_entry_le v he hk1 2 2)).trans_eq (mul_one e)
    · exact (mul_le_mul' (v_offdiag_le v hk1 (by decide)) (v_entry_le v he hk1 2 1)).trans_eq (mul_one e)
  have hzv : Valued.v z ≤ e := by
    rw [hz, map_div₀, hDv, div_one]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul]
    · exact (mul_le_mul' (v_offdiag_le v hk1 (by decide)) (v_entry_le v he hk1 1 1)).trans_eq (mul_one e)
    · exact (mul_le_mul' (v_offdiag_le v hk1 (by decide)) (v_entry_le v he hk1 1 2)).trans_eq (mul_one e)
  have hu : radicalP12 ![x, z] ∈ Kc v e he := by
    have e0 : Valued.v (0 : Fv v) ≤ e := by rw [map_zero]; exact zero_le'
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp only [mat, radicalP12_coe]
      fin_cases i <;> fin_cases j <;> simp [e0, hxv, hzv]
    · have : mat v (radicalP12 ![x, z])⁻¹ = !![1, -x, x * 0 - z; 0, 1, -0; 0, 0, 1] := rfl
      rw [this]
      fin_cases i <;> fin_cases j <;> simp [e0, hxv, hzv, Valuation.map_neg]
  set p : LocalGL3 v := (radicalP12 ![x, z])⁻¹ * k with hp
  have hpK : p ∈ Kc v e he := (Kc v e he).mul_mem ((Kc v e he).inv_mem hu) ⟨hk1, hk2⟩
  have hkp : k = radicalP12 ![x, z] * p := by rw [hp, mul_inv_cancel_left]
  have hpinv : mat v (radicalP12 ![x, z])⁻¹ = !![1, -x, x * 0 - z; 0, 1, -0; 0, 0, 1] := rfl
  have hp01 : mat v p 0 1 = 0 := by
    rw [hp, mat_mul, hpinv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hx, hz]
    field_simp
    rw [hD]; ring
  have hp02 : mat v p 0 2 = 0 := by
    rw [hp, mat_mul, hpinv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hx, hz]
    field_simp
    rw [hD]; ring
  have hp00 : mat v p 0 0 ≠ 0 := ne_zero_of_v_sub_one_lt v ((v_diag_sub_one_le v hpK.1 0).trans_lt he1)
  have hinvrow : ∀ j : Fin 3, j ≠ 0 → mat v p⁻¹ 0 j = 0 := by
    intro j hj
    have h := mat_mul v p p⁻¹ 0 j
    rw [mul_inv_cancel, show mat v (1 : LocalGL3 v) = 1 from Units.val_one, Matrix.one_apply_ne hj.symm, hp01, hp02,
      zero_mul, zero_mul, add_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hp00
  exact ⟨![x, z], p, hkp, hpK, hp01, hp02, hinvrow 1 (by decide), hinvrow 2 (by decide)⟩

theorem factor21 {e : WithZero (Multiplicative ℤ)} (he : e ≤ 1) (he1 : e < 1) {k : LocalGL3 v}
    (hk : k ∈ Kc v e he) :
    ∃ (w : Fin 2 → Fv v) (p : LocalGL3 v), k = radicalP21 w * p ∧ p ∈ Kc v e he ∧
      mat v p 0 2 = 0 ∧ mat v p 1 2 = 0 ∧ mat v p⁻¹ 0 2 = 0 ∧ mat v p⁻¹ 1 2 = 0 := by
  obtain ⟨hk1, hk2⟩ := hk
  have h22v : Valued.v (mat v k 2 2) = 1 := v_eq_one_of_v_sub_one_lt v ((v_diag_sub_one_le v hk1 2).trans_lt he1)
  have h22 : mat v k 2 2 ≠ 0 := ne_zero_of_v_sub_one_lt v ((v_diag_sub_one_le v hk1 2).trans_lt he1)
  set a : Fv v := mat v k 0 2 / mat v k 2 2 with ha
  set b : Fv v := mat v k 1 2 / mat v k 2 2 with hb
  have hav : Valued.v a ≤ e := by rw [ha, map_div₀, h22v, div_one]; exact v_offdiag_le v hk1 (by decide)
  have hbv : Valued.v b ≤ e := by rw [hb, map_div₀, h22v, div_one]; exact v_offdiag_le v hk1 (by decide)
  have hu : radicalP21 ![a, b] ∈ Kc v e he := by
    have e0 : Valued.v (0 : Fv v) ≤ e := by rw [map_zero]; exact zero_le'
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp only [mat, radicalP21_coe]
      fin_cases i <;> fin_cases j <;> simp [e0, hav, hbv]
    · have : mat v (radicalP21 ![a, b])⁻¹ = !![1, -0, 0 * b - a; 0, 1, -b; 0, 0, 1] := rfl
      rw [this]
      fin_cases i <;> fin_cases j <;> simp [e0, hav, hbv, Valuation.map_neg]
  set p : LocalGL3 v := (radicalP21 ![a, b])⁻¹ * k with hp
  have hpK : p ∈ Kc v e he := (Kc v e he).mul_mem ((Kc v e he).inv_mem hu) ⟨hk1, hk2⟩
  have hkp : k = radicalP21 ![a, b] * p := by rw [hp, mul_inv_cancel_left]
  have hpinv : mat v (radicalP21 ![a, b])⁻¹ = !![1, -0, 0 * b - a; 0, 1, -b; 0, 0, 1] := rfl
  have hp02 : mat v p 0 2 = 0 := by
    rw [hp, mat_mul, hpinv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [ha]
    field_simp
    ring
  have hp12 : mat v p 1 2 = 0 := by
    rw [hp, mat_mul, hpinv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hb]
    field_simp
    ring
  have hp22 : mat v p 2 2 ≠ 0 := ne_zero_of_v_sub_one_lt v ((v_diag_sub_one_le v hpK.1 2).trans_lt he1)
  have hinvcol : ∀ i : Fin 3, i ≠ 2 → mat v p⁻¹ i 2 = 0 := by
    intro i hi
    have h := mat_mul v p⁻¹ p i 2
    rw [inv_mul_cancel, show mat v (1 : LocalGL3 v) = 1 from Units.val_one, Matrix.one_apply_ne hi, hp02, hp12,
      mul_zero, mul_zero, zero_add, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hp22
  exact ⟨![a, b], p, hkp, hpK, hp02, hp12, hinvcol 0 (by decide), hinvcol 1 (by decide)⟩

end SlJ2

namespace SlJ2

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

def VN (W : LocalGL3 v → ℂ) (rad : (Fin 2 → Fv v) → LocalGL3 v) : Submodule ℂ (LocalGL3 v → ℂ) :=
  Submodule.span ℂ {F : LocalGL3 v → ℂ | ∃ (w : Fin 2 → Fv v) (G : LocalGL3 v → ℂ),
    G ∈ gl3CyclicSubspace W ∧ F = fun g => G (g * rad w) - G g}

theorem sub_mem_VN {W : LocalGL3 v → ℂ} {rad : (Fin 2 → Fv v) → LocalGL3 v} {G : LocalGL3 v → ℂ}
    (hG : G ∈ gl3CyclicSubspace W) (w : Fin 2 → Fv v) :
    (fun g => G (g * rad w) - G g) ∈ VN v W rad :=
  Submodule.subset_span ⟨w, G, hG, rfl⟩

theorem coeff_sum_monomial (d : ℕ) (c : ℕ → ℂ) (m : ℕ) :
    (∑ n ∈ Finset.range (d + 1), Polynomial.monomial n (c n)).coeff m = if m < d + 1 then c m else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (d + 1)) m c]
  simp only [Finset.mem_range]

theorem core (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (Φ : LocalGL3 v → ℂ) (hΦ : Φ ∈ gl3CyclicSubspace W)
    (T : LocalGL3 v) (rad : (Fin 2 → Fv v) → LocalGL3 v)
    (K : Subgroup (LocalGL3 v)) (hKc : IsCompact (K : Set (LocalGL3 v))) (hKo : IsOpen (K : Set (LocalGL3 v)))
    (hKΦ : ∀ k ∈ K, ∀ g : LocalGL3 v, Φ (g * k) = Φ g)
    (hfac : ∀ k ∈ K, ∃ (w : Fin 2 → Fv v) (p : LocalGL3 v), k = rad w * p ∧ ∀ a : ℕ, (T ^ a)⁻¹ * p * T ^ a ∈ K) :
    ∃ C : Polynomial ℂ, C ≠ 0 ∧
      (∑ i ∈ Finset.range (C.natDegree + 1), C.coeff i • (fun g : LocalGL3 v => Φ (g * T ^ i))) ∈ VN v W rad := by
  classical

  set Fa : ℕ → (LocalGL3 v → ℂ) := fun a g => Φ (g * T ^ a) with hFa
  have hFa_mem : ∀ a, Fa a ∈ gl3CyclicSubspace W := fun a =>
    gl3AmbientRightTranslate_mem_gl3CyclicSubspace W (T ^ a) hΦ

  have hdiff : ∀ a, ∀ k ∈ K, (fun g => Fa a (g * k) - Fa a g) ∈ VN v W rad := by
    intro a k hk
    obtain ⟨w, p, hkp, hp⟩ := hfac k hk
    have e : (fun g => Fa a (g * k) - Fa a g) = fun g => Fa a (g * rad w) - Fa a g := by
      funext g
      simp only [hFa]
      rw [hkp]
      have e1 : g * (rad w * p) * T ^ a = (g * rad w * T ^ a) * ((T ^ a)⁻¹ * p * T ^ a) := by group
      rw [e1, hKΦ _ (hp a)]
    rw [e]
    exact sub_mem_VN v (hFa_mem a) w

  have hFo : ∀ a, IsOpen ((gl3RightStabilizer v (Fa a) : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := fun a =>
    isOpen_gl3RightStabilizer_of_mem_gl3CyclicSubspace v hsm (hFa_mem a)
  set N : ℕ → ℕ := fun a => Nat.card (K ⧸ (gl3RightStabilizer v (Fa a)).subgroupOf K) with hN
  have hNpos : ∀ a, 0 < N a := fun a => card_pos_of_finite v hKc (hFo a)
  set Ψ : ℕ → (LocalGL3 v → ℂ) := fun a => ((N a : ℂ))⁻¹ • gl3FiniteAverage v K (Fa a) with hΨ
  have hΨ_mem : ∀ a, Ψ a ∈ gl3CyclicSubspace W := fun a =>
    Submodule.smul_mem _ _ (gl3FiniteAverage_mem v hKc (hFo a) (hFa_mem a))
  have hΨ_fix : ∀ a, ∀ k ∈ K, ∀ g : LocalGL3 v, Ψ a (g * k) = Ψ a g := fun a k hk g => by
    simp only [hΨ, Pi.smul_apply, gl3FiniteAverage_mul_mem v hKc (hFo a) hk g]
  have hΨ_sub : ∀ a, Ψ a - Fa a ∈ VN v W rad := by
    intro a
    haveI := finite_quotient_of_isCompact_of_isOpen v hKc (hFo a)
    letI : Fintype (K ⧸ (gl3RightStabilizer v (Fa a)).subgroupOf K) := Fintype.ofFinite _
    have havg : gl3FiniteAverage v K (Fa a) =
        ∑ q : K ⧸ (gl3RightStabilizer v (Fa a)).subgroupOf K,
          gl3AmbientRightTranslate (R := ℂ) (q.out : LocalGL3 v) (Fa a) := by
      unfold gl3FiniteAverage; rw [finsum_eq_sum_of_fintype]
    have hcard : (Fintype.card (K ⧸ (gl3RightStabilizer v (Fa a)).subgroupOf K) : ℂ) = (N a : ℂ) := by
      simp only [hN, Nat.card_eq_fintype_card]
    have hN0 : (N a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hNpos a).ne'
    have e : Ψ a - Fa a = ((N a : ℂ))⁻¹ • ∑ q : K ⧸ (gl3RightStabilizer v (Fa a)).subgroupOf K,
        (gl3AmbientRightTranslate (R := ℂ) (q.out : LocalGL3 v) (Fa a) - Fa a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, hcard, ← havg,
        smul_sub, smul_smul, inv_mul_cancel₀ hN0, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    have e2 : gl3AmbientRightTranslate (R := ℂ) (q.out : LocalGL3 v) (Fa a) - Fa a =
        fun g => Fa a (g * (q.out : LocalGL3 v)) - Fa a g := by
      funext g; rfl
    rw [e2]
    exact hdiff a _ (q.out).2

  obtain ⟨B, hB⟩ := hadm K hKo
  have hΨ_span : ∀ a, Ψ a ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := fun a =>
    hB _ (hΨ_mem a) (hΨ_fix a)
  set d : ℕ := B.card with hd
  let fam : Fin (d + 1) → ↥(Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) := fun i => ⟨Ψ i, hΨ_span i⟩
  have hdep : ¬ LinearIndependent ℂ fam := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    have h2 : Module.finrank ℂ ↥(Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ≤ d :=
      finrank_span_finset_le_card B
    rw [Fintype.card_fin] at h1
    omega
  obtain ⟨c, hc0, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hsumΨ : ∑ i : Fin (d + 1), c i • Ψ i = 0 := by
    have h := congrArg (fun x : ↥(Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) => (x : LocalGL3 v → ℂ)) hc0
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using h

  set c' : ℕ → ℂ := fun n => if h : n < d + 1 then c ⟨n, h⟩ else 0 with hc'
  have hc'_lt : ∀ i : Fin (d + 1), c' i = c i := fun i => by
    simp only [hc', dif_pos i.2]
  have hc'_ge : ∀ m : ℕ, ¬ m < d + 1 → c' m = 0 := fun m hm => by
    simp only [hc', dif_neg hm]
  set C : Polynomial ℂ := ∑ n ∈ Finset.range (d + 1), Polynomial.monomial n (c' n) with hC
  have hcoeff : ∀ m, C.coeff m = c' m := by
    intro m
    rw [hC, coeff_sum_monomial]
    by_cases hm : m < d + 1
    · rw [if_pos hm]
    · rw [if_neg hm, hc'_ge m hm]
  have hCdeg : C.natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hcoeff, hc'_ge m (by omega)]
  refine ⟨C, ?_, ?_⟩
  · intro h0
    apply hi₀
    have := hcoeff i₀
    rw [h0, Polynomial.coeff_zero, hc'_lt i₀] at this
    exact this.symm
  ·
    have hS : (∑ i ∈ Finset.range (C.natDegree + 1), C.coeff i • (fun g : LocalGL3 v => Φ (g * T ^ i))) =
        ∑ i : Fin (d + 1), c i • Fa i := by
      have h1 : (∑ i ∈ Finset.range (C.natDegree + 1), C.coeff i • Fa i) =
          ∑ i ∈ Finset.range (d + 1), C.coeff i • Fa i := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
        rw [Finset.mem_range, not_lt] at hi
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
      rw [show (fun i => C.coeff i • (fun g : LocalGL3 v => Φ (g * T ^ i))) = fun i => C.coeff i • Fa i from rfl, h1,
        Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff, hc'_lt i]
    rw [hS]
    have e : ∑ i : Fin (d + 1), c i • Fa i = ∑ i : Fin (d + 1), c i • (Fa i - Ψ i) := by
      rw [← sub_zero (∑ i : Fin (d + 1), c i • Fa i), ← hsumΨ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_sub]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := (VN v W rad).neg_mem (hΨ_sub i)
    rwa [neg_sub] at this

end SlJ2

end

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : LocalGL3 v → ℂ) (hΦ : Φ ∈ gl3CyclicSubspace W) :
    (∃ C : Polynomial ℂ, C ≠ 0 ∧
      (∑ i ∈ Finset.range (C.natDegree + 1),
          C.coeff i • (fun g : LocalGL3 v =>
            Φ (g * iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) ^ i))) ∈
        Submodule.span ℂ {F : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
          G ∈ gl3CyclicSubspace W ∧ F = fun g => G (g * radicalP12 w) - G g}) ∧
    (∃ C : Polynomial ℂ, C ≠ 0 ∧
      (∑ i ∈ Finset.range (C.natDegree + 1),
          C.coeff i • (fun g : LocalGL3 v =>
            Φ (g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ i))) ∈
        Submodule.span ℂ {F : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
          G ∈ gl3CyclicSubspace W ∧ F = fun g => G (g * radicalP21 w) - G g}) := by

  set π : v.adicCompletion ℚ := algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ with hπdef
  have hπv : Valued.v π = WithZero.exp (-1 : ℤ) := hϖ

  have hSo : IsOpen ((SlJ2.gl3RightStabilizer v Φ : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) :=
    SlJ2.isOpen_gl3RightStabilizer_of_mem_gl3CyclicSubspace v hsm hΦ
  obtain ⟨n, hn⟩ := SlJ2.exists_Kc_le v hπv hSo
  have he : Valued.v (π ^ (n + 1)) ≤ 1 := SlJ2.v_pow_le_one v hπv (n + 1)
  have he1 : Valued.v (π ^ (n + 1)) < 1 := SlJ2.v_pow_lt_one v hπv (by omega)
  set K : Subgroup (LocalGL3 v) := SlJ2.Kc v (Valued.v (π ^ (n + 1))) he with hKdef
  have hKc : IsCompact (K : Set (LocalGL3 v)) := SlJ2.isCompact_Kc v (π ^ (n + 1)) he
  have hKo : IsOpen (K : Set (LocalGL3 v)) := SlJ2.isOpen_Kc v (pow_ne_zero _ hπ) he
  have hKΦ : ∀ k ∈ K, ∀ g : LocalGL3 v, Φ (g * k) = Φ g := fun k hk g =>
    (SlJ2.mem_gl3RightStabilizer_iff v).1 (hn hk) g
  set u : (v.adicCompletion ℚ)ˣ := Units.mk0 π hπ with hudef
  have hu_pow : ∀ a : ℕ, Valued.v ((u ^ a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 := fun a => by
    rw [Units.val_pow_eq_pow_val, hudef, Units.val_mk0]; exact SlJ2.v_pow_le_one v hπv a
  refine ⟨?_, ?_⟩
  ·
    refine SlJ2.core v W hsm hadm Φ hΦ (iotaGL (diagUnitGL2 u)) radicalP12 K hKc hKo hKΦ fun k hk => ?_
    obtain ⟨w, p, hkp, hpK, h01, h02, h01', h02'⟩ := SlJ2.factor12 v he he1 hk
    refine ⟨w, p, hkp, fun a => ?_⟩
    have hT : iotaGL (diagUnitGL2 u) ^ a = iotaGL (SlJ2.dU v (u ^ a) 1) := by
      rw [← map_pow, hudef, SlJ2.diagUnitGL2_pow]
    have hTi : (iotaGL (diagUnitGL2 u) ^ a)⁻¹ = iotaGL (SlJ2.dU v (u ^ a)⁻¹ 1) := by
      rw [hT, ← map_inv, SlJ2.dU_inv, inv_one]
    rw [hTi, hT]
    refine ⟨SlJ2.congOne_conj12 v hpK.1 h01 h02 (hu_pow a), ?_⟩
    have hi := SlJ2.inv_conj v (u ^ a) 1 p
    rw [inv_one] at hi
    show SlJ2.CongOne v _ (SlJ2.mat v (iotaGL (SlJ2.dU v (u ^ a)⁻¹ 1) * p * iotaGL (SlJ2.dU v (u ^ a) 1))⁻¹)
    rw [hi]
    exact SlJ2.congOne_conj12 v hpK.2 h01' h02' (hu_pow a)
  ·
    refine SlJ2.core v W hsm hadm Φ hΦ (iotaGL (UnramifiedWhittaker.scalarPi π hπ)) radicalP21 K hKc hKo hKΦ
      fun k hk => ?_
    obtain ⟨w, p, hkp, hpK, h02, h12, h02', h12'⟩ := SlJ2.factor21 v he he1 hk
    refine ⟨w, p, hkp, fun a => ?_⟩
    have hT : iotaGL (UnramifiedWhittaker.scalarPi π hπ) ^ a = iotaGL (SlJ2.dU v (u ^ a) (u ^ a)) := by
      rw [← map_pow, hudef, SlJ2.scalarPi_pow]
    have hTi : (iotaGL (UnramifiedWhittaker.scalarPi π hπ) ^ a)⁻¹ = iotaGL (SlJ2.dU v (u ^ a)⁻¹ (u ^ a)⁻¹) := by
      rw [hT, ← map_inv, SlJ2.dU_inv]
    rw [hTi, hT]
    refine ⟨SlJ2.congOne_conj21 v hpK.1 h02 h12 (hu_pow a), ?_⟩
    show SlJ2.CongOne v _ (SlJ2.mat v (iotaGL (SlJ2.dU v (u ^ a)⁻¹ (u ^ a)⁻¹) * p * iotaGL (SlJ2.dU v (u ^ a) (u ^ a)))⁻¹)
    rw [SlJ2.inv_conj]
    exact SlJ2.congOne_conj21 v hpK.2 h02' h12' (hu_pow a)

end S_LanglandsTunnell_CubicInduction_exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible (solution)
