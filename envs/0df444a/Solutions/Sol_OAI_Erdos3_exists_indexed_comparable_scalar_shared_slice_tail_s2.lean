-- Prove2me | solution 1 for OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:46:21.3895+00:00
-- url     : https://prove2.me/submissions/e47605aa-3808-454a-969f-0a7ad1a4c402

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Theorems.Thm_OAI_Erdos3_exists_comparableScalarSelectedBudget_s2
import Theorems.Thm_OAI_Erdos3_exists_unconditioned_joint_scalar_transfer_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem baseArrayJoin_injective {K I X : Type*} (tail : K × I → X) :
    Function.Injective (baseArrayJoin tail) := by
  intro b c he
  funext i
  exact congrFun he (none,i)

theorem independentProductPMF_base_split {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : K × I => p (some k.1,k.2))).bind
        (fun tail => (independentProductPMF (fun i => p (none,i))).map (baseArrayJoin tail)) := by
  ext z
  let tail := fun k : K × I => z (some k.1,k.2)
  let base := fun i : I => z (none,i)
  have hz : baseArrayJoin tail base = z := baseArrayJoin_eta z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (baseArrayJoin_injective tail)]
    simp only [independentProductPMF_apply, Fintype.prod_prod_type, Fintype.prod_option, baseArrayJoin]
    exact mul_comm _ _
  · intro other hother
    have hr : baseArrayJoin tail base ∉ Set.range (baseArrayJoin other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      exact congrFun he (some k.1,k.2)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_base_cap {K I X Y : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) (f : (Option K × I → X) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i) (hp : ∀ i x, (p (none,i) x).toReal ≤ C i) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ ∏ i, C i := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp_rw [PMF.map_comp]
  apply pmf_bind_injective_toReal_cap _ _ _ hf (Finset.prod_nonneg (fun i _ => hC i))
  intro base
  rw [independentProductPMF_toReal]
  exact Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hp i (base i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductPMF_base_cap {K I Y : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (Option K × I → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S (none,i)) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ ∏ i, 2 / S (none,i) := by
  rw [shiftedSmoothProductPMF_eq_independent]
  apply independentProductPMF_base_cap _ f hf (fun i => 2 / S (none,i))
    (fun i => div_nonneg (by norm_num) (hS (none,i)).le)
  intro i k
  exact shiftedSmoothCoefficientPMF_le (a (none,i)) (hbase i) k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

omit [Fintype X] [DecidableEq X] in
theorem fullSliceRectangle_endpoint_bounds (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) {L C : ℝ} (hL : 0 < L)
    (hN : ∀ i, (N i : ℝ) ≤ C * L) (i : X) :
    |(S.start i : ℝ) / L| ≤ C ∧
      |((S.start i : ℝ) + (q : ℝ) * S.length i) / L| ≤ C + q / L := by
  have hstart : S.start i < N i := by simpa using S.inside i 0 (hlen i)
  have hlast := S.inside i (S.length i - 1) (by have := hlen i; omega)
  have hend : S.start i + q * S.length i < N i + q := by
    have he : S.start i + q * S.length i =
        (S.start i + q * (S.length i - 1)) + q := by
      have hl : S.length i = (S.length i - 1) + 1 := by have := hlen i; omega
      conv_lhs => rw [hl]
      ring
    rw [he]
    omega
  have hstartR : (S.start i : ℝ) < N i := by exact_mod_cast hstart
  have hendR : (S.start i : ℝ) + (q : ℝ) * S.length i < (N i : ℝ) + q := by
    exact_mod_cast hend
  constructor
  · rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hL.le)]
    exact (div_le_iff₀ hL).mpr (hstartR.le.trans (hN i))
  · rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hL).mpr
    rw [add_mul, div_mul_cancel₀ _ hL.ne']
    linarith [hN i]

omit [Fintype X] [DecidableEq X] in
theorem fullSliceRectangle_endpoint_bounds_two (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 2 ≤ S.length i) {L C : ℝ} (hL : 0 < L)
    (hN : ∀ i, (N i : ℝ) ≤ C * L) (i : X) :
    |(S.start i : ℝ) / L| ≤ C ∧
      |((S.start i : ℝ) + (q : ℝ) * S.length i) / L| ≤ 2 * C := by
  have hbase := fullSliceRectangle_endpoint_bounds S (fun i => by have := hlen i; omega) hL hN i
  have hqN : q < N i := by
    have h := S.inside i 1 (by have := hlen i; omega)
    omega
  have hqR : (q : ℝ) ≤ C * L :=
    (show (q : ℝ) ≤ (N i : ℝ) by exact_mod_cast hqN.le).trans (hN i)
  have hqL : (q : ℝ) / L ≤ C := (div_le_iff₀ hL).mpr hqR
  exact ⟨hbase.1, hbase.2.trans (by linarith)⟩

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBaseInjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem residueLatticeArray_baseArrayJoin {K I : Type*}
    (residue : Option K × I → ℤ) (modulus : I → ℕ) (tail : K × I → ℤ) (base : I → ℤ) :
    residueLatticeArray residue modulus (baseArrayJoin tail base) =
      baseArrayJoin (fun k => residue (some k.1,k.2) + (modulus k.2 : ℤ)*tail k)
        (fun i => residue (none,i) + (modulus i : ℤ)*base i) := by
  funext z
  rcases z with ⟨k,i⟩
  cases k <;> rfl

theorem physicalAffineSite_residue_base_injective {K I : Type*} [Fintype K]
    (root : K → ℤ) (residue : Option K × I → ℤ)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (tail : K × I → ℤ) :
    Function.Injective (fun base =>
      physicalAffineSite root (residueLatticeArray residue modulus (baseArrayJoin tail base))) := by
  intro b c he
  funext i
  have h := congrFun he i
  simp only [residueLatticeArray_baseArrayJoin, physicalAffineSite_baseArrayJoin_apply] at h
  have hb : residue (none,i) + (modulus i : ℤ)*b i =
      residue (none,i) + (modulus i : ℤ)*c i := by exact_mod_cast add_right_cancel h
  exact mul_left_cancel₀ (by exact_mod_cast (hmodulus i).ne' : (modulus i : ℤ) ≠ 0)
    (add_left_cancel hb)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePhysicalCap
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem residueSmoothPMF_physical_cap {K I : Type*} [Fintype K] [Fintype I]
    (root : K → ℤ) (residue : Option K × I → ℤ)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus W))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W (none,i))
    (y : I → ℝ) :
    ((residueSmoothPMF residue modulus hmodulus W hW hZ).map (physicalAffineSite root) y).toReal ≤
      ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  rw [residueSmoothPMF, PMF.map_comp, residueSmoothIndexPMF]
  have h := shiftedSmoothProductPMF_base_cap (residueProfileCenter residue modulus)
    (residueProfileWidth modulus W) (residueProfileWidth_pos modulus W hmodulus hW) hZ
    (physicalAffineSite root ∘ residueLatticeArray residue modulus)
    (physicalAffineSite_residue_base_injective root residue modulus hmodulus) hbase y
  simpa only [residueProfileWidth, div_div_eq_mul_div] using h

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedPhysicalReferenceCap
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
variable (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (hc : ∀ r : T, 0 < shiftedSmoothProductMass
  (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus W))
variable (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W (none,i))

include hmodulus hT hc hbase in
theorem selectedResidueSmoothPMF_physical_cap (y : I → ℝ) :
    ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal ≤
      ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  obtain ⟨_, h⟩ := selectedResidueSmoothPMF_bound_of_cells (ε := ∏ i, 2*(modulus i : ℝ)/W (none,i))
    modulus hmodulus T hT W hW hc
    (fun z => if physicalAffineSite root z = y then (1 : ℂ) else 0)
    (by
      intro r
      exact (pmf_point_indicator_norm _ (physicalAffineSite root) y).trans_le
        (residueSmoothPMF_physical_cap root (columnResidueRepresentative modulus r.val)
          modulus hmodulus W hW (hc r) hbase y))
  exact (pmf_point_indicator_norm _ (physicalAffineSite root) y).symm.trans_le h

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

theorem exists_selectedResidue_physical_cap {K I : Type*} [Fintype K] [Fintype I]
    (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
      ∀ y, ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal ≤
        ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  have hc (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus W) :=
    shiftedSmoothProductMass_pos_of_scales _ _ hscale
  have hZ := selectedResidueSmoothWeight_mass_pos modulus T hT W hW (fun r => by
    rw [← residueSmoothWeight_mass _ modulus hmodulus W hW]
    exact hc r)
  exact ⟨hZ, selectedResidueSmoothPMF_physical_cap root modulus hmodulus T hT W hW hZ hc
    (fun i => hscale (none,i))⟩

end BooleanCubeKernel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalJointFrameGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped Classical

theorem jointFrameSource_nonempty {K I : Type*} (N : I → ℕ)
    (hN : ∀ i, 0 < N i) (width : Option K × I → ℝ) (hw : ∀ t, 0 ≤ width t) :
    ∀ t, jointFrameSourceLo width t < jointFrameSourceHi N width t := by
  rintro ⟨_ | k, i⟩
  · simpa [jointFrameSourceLo, jointFrameSourceHi] using hN i
  · have hc : (0 : ℤ) ≤ ⌈width (some k,i)⌉ := Int.ceil_nonneg (hw _)
    dsimp [jointFrameSourceLo, jointFrameSourceHi]
    omega

theorem jointIntegerFrame_mem_sourceBox {K I : Type*} [Fintype K] [Fintype I]
    [DecidableEq I] (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i ≤ N i)
    (width : Option K × I → ℝ) (hroot : ∀ i, width (none,i) ≤ (margin i : ℝ))
    (z : trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) :
    ∀ t, jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈
      Finset.Ico (jointFrameSourceLo width t) (jointFrameSourceHi N width t) := by
  have hb := rectangularWeightIndices_zero_bound width z.2.property
  have hconstant : (fun i => z.1.val i + z.2.val (none,i)) ∈ integerBox N := by
    apply trimmedIntegerBox_add_mem N margin hmargin z.1.property
    intro i
    have h := (hb (none,i)).trans (hroot i)
    exact_mod_cast h
  rintro ⟨_ | k, i⟩
  · simpa only [jointIntegerFrame, jointFrameSourceLo, jointFrameSourceHi,
      Finset.mem_Ico] using (mem_integerBox N _).mp hconstant i
  · have hbound : |z.2.val (some k,i)| ≤ ⌈width (some k,i)⌉ := by
      exact_mod_cast (hb (some k,i)).trans (Int.le_ceil _)
    have hparts := abs_le.mp hbound
    simp only [jointIntegerFrame, jointFrameSourceLo, jointFrameSourceHi, Finset.mem_Ico]
    omega

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped Classical

theorem jointFrameSource_window_bounds {K I : Type*} [Fintype K] [Fintype I]
    (N : I → ℕ) (width : Option K × I → ℝ) {L : ℝ} (hL : 0 < L)
    (hwide : ∀ k i, 1 ≤ width (some k, i))
    (hsmall : ∀ k i, 3 * width (some k, i) ≤ (N i : ℝ) / L) :
    (∀ z ∈ Fintype.piFinset (fun t =>
        Finset.Ico (jointFrameSourceLo width t) (jointFrameSourceHi N width t)),
      ∀ t, |(z t : ℝ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k i, |(jointFrameSourceLo width (some k, i) : ℝ)| ≤ 2 * (N i : ℝ) / L) ∧
    (∀ k i, |(jointFrameSourceHi N width (some k, i) : ℝ)| ≤ 2 * (N i : ℝ) / L) := by
  have hceil0 (k : K) (i : I) : (0 : ℝ) ≤ (⌈width (some k, i)⌉ : ℤ) := by
    exact_mod_cast Int.ceil_nonneg (zero_le_one.trans (hwide k i))
  have hceil (k : K) (i : I) :
      (⌈width (some k, i)⌉ : ℝ) + 1 ≤ (N i : ℝ) / L := by
    have hc := Int.ceil_lt_add_one (width (some k, i))
    have hw := hwide k i
    have hs := hsmall k i
    linarith
  have hdouble (i : I) : (N i : ℝ) / L ≤ 2 * (N i : ℝ) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith [Nat.cast_nonneg (N i) (α := ℝ)]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz t
    have ht := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hz t)
    rcases t with ⟨_ | k, i⟩
    · simp only [jointFrameSourceLo, jointFrameSourceHi] at ht
      have hz0 : (0 : ℝ) ≤ z (none, i) := by exact_mod_cast ht.1
      have hzN : (z (none, i) : ℝ) < N i := by exact_mod_cast ht.2
      simpa only [smoothPairCoefficientScale, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
        abs_of_nonneg hz0] using hzN.le
    · have hlo : -(⌈width (some k, i)⌉ : ℝ) ≤ z (some k, i) := by
        exact_mod_cast ht.1
      have hhi : (z (some k, i) : ℝ) < (⌈width (some k, i)⌉ : ℝ) + 1 := by
        exact_mod_cast ht.2
      have hzbound : |(z (some k, i) : ℝ)| ≤ (N i : ℝ) / L := by
        apply abs_le.mpr
        constructor <;> linarith [hceil k i]
      have hscale : smoothPairCoefficientScale (2 * (N i : ℝ)) L (some k) / 2 =
          (N i : ℝ) / L := by
        dsimp [smoothPairCoefficientScale]
        ring
      rwa [hscale]
  · intro k i
    simp only [jointFrameSourceLo, Int.cast_neg, abs_neg,
      abs_of_nonneg (hceil0 k i)]
    exact (by linarith [hceil k i] : (⌈width (some k, i)⌉ : ℝ) ≤ (N i : ℝ) / L).trans
      (hdouble i)
  · intro k i
    simp only [jointFrameSourceHi, Int.cast_add, Int.cast_one,
      abs_of_nonneg (add_nonneg (hceil0 k i) zero_le_one)]
    exact (hceil k i).trans (hdouble i)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

private theorem jointFrame_slope_side_cap {W : ℝ} (hW : 1 ≤ W) :
    0 ≤ (2 * (⌈W⌉ : ℝ) + 1) * (2 / W) ∧
      (2 * (⌈W⌉ : ℝ) + 1) * (2 / W) ≤ 10 := by
  have hW0 : 0 < W := by linarith
  have hceil0 : (0 : ℝ) ≤ (⌈W⌉ : ℤ) := by exact_mod_cast Int.ceil_nonneg hW0.le
  constructor
  · positivity
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hW0).mpr
    have hc := Int.ceil_lt_add_one W
    nlinarith

theorem jointFrameSource_volume_cap_le {K I : Type*} [Fintype K] [Fintype I]
    (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (hloss : (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1/2)
    (width : Option K × I → ℝ) (hwidth : ∀ t : K × I, 1 ≤ width (some t.1,t.2)) :
    (∏ t, ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) *
        (((trimmedIntegerBox N margin).card : ℝ)⁻¹ *
          ∏ t : K × I, 2 / width (some t.1,t.2)) ≤ 2 * 10 ^ Fintype.card (K × I) := by
  have hvolume :
      (∏ t, ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) =
      (∏ i, (N i : ℝ)) *
        ∏ t : K × I, (2 * (⌈width (some t.1,t.2)⌉ : ℝ) + 1) := by
    rw [Fintype.prod_prod_type, Fintype.prod_option]
    simp only [jointFrameSourceHi, jointFrameSourceLo, sub_zero, Int.cast_natCast,
      Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_one]
    rw [Fintype.prod_prod_type]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    apply Finset.prod_congr rfl
    intro i _
    ring
  have hproduct :
      (∏ t : K × I, (2 * (⌈width (some t.1,t.2)⌉ : ℝ) + 1) *
        (2 / width (some t.1,t.2))) ≤ 10 ^ Fintype.card (K × I) := by
    calc
      _ ≤ ∏ _t : K × I, (10 : ℝ) :=
        Finset.prod_le_prod (fun t _ => (jointFrame_slope_side_cap (hwidth t)).1)
          (fun t _ => (jointFrame_slope_side_cap (hwidth t)).2)
      _ = _ := by simp
  calc
    _ = (((integerBox N).card : ℝ) / (trimmedIntegerBox N margin).card) *
        ∏ t : K × I, (2 * (⌈width (some t.1,t.2)⌉ : ℝ) + 1) *
          (2 / width (some t.1,t.2)) := by
      rw [hvolume, card_integerBox, Nat.cast_prod, Finset.prod_mul_distrib, div_eq_mul_inv]
      ring
    _ ≤ 2 * 10 ^ Fintype.card (K × I) :=
      mul_le_mul (trimmedIntegerBox_card_ratio_le_two N margin hmargin hloss) hproduct
        (Finset.prod_nonneg (fun t _ => (jointFrame_slope_side_cap (hwidth t)).1))
        (by norm_num)

theorem jointFrameSource_volume_exp_bound (d : ℕ) {p : ℝ}
    (hp : 4 * ((d : ℝ) + 1) ≤ p) :
    2 * (10 : ℝ)^d ≤ Real.exp p := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 4
    norm_num [← Real.exp_nat_mul] at hpow ⊢
    exact hpow
  calc
    _ ≤ Real.exp 4 * (Real.exp 4)^d := by
      gcongr <;> linarith
    _ = Real.exp (4 * ((d : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hp

theorem jointFrameSource_volume_cap_le_exp {K I : Type*} [Fintype K] [Fintype I]
    (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (hloss : (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1/2)
    (width : Option K × I → ℝ) (hwidth : ∀ t : K × I, 1 ≤ width (some t.1,t.2))
    {p : ℝ} (hp : 4 * ((Fintype.card (K × I) : ℝ) + 1) ≤ p) :
    (∏ t, ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) *
        (((trimmedIntegerBox N margin).card : ℝ)⁻¹ *
          ∏ t : K × I, 2 / width (some t.1,t.2)) ≤ Real.exp p :=
  (jointFrameSource_volume_cap_le N margin hmargin hloss width hwidth).trans
    (jointFrameSource_volume_exp_bound _ hp)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

theorem canonicalJointFrameWindowConstant_two_le (d : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    2 ≤ canonicalJointFrameWindowConstant d τ := by
  unfold canonicalJointFrameWindowConstant
  apply (le_div_iff₀ hτ).mpr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

theorem canonicalJointFrame_slope_small {K I : Type*} (N : I → ℕ)
    {L Wsite τ : ℝ} (hL : 1 ≤ L) (hW : L ≤ Wsite) (_hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (k : K) (i : I) :
    3 * trimmedSpatialWidths Wsite τ N (some k,i) ≤ (N i : ℝ) / L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hden : 0 < 8 * (1 + Wsite) := by linarith
  have hc : 3 * τ * L ≤ 8 * (1 + Wsite) := by
    have hh := mul_le_mul_of_nonneg_right hτ1 hLp.le
    nlinarith
  have hN : (0 : ℝ) ≤ N i := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hc hN
  dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
  rw [le_div_iff₀ hLp]
  have hdiv : (3 * τ * L * (N i : ℝ)) / (8 * (1 + Wsite)) ≤ (N i : ℝ) :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hmul)
  calc
    _ = (3 * τ * L * (N i : ℝ)) / (8 * (1 + Wsite)) := by ring
    _ ≤ (N i : ℝ) := hdiv

theorem canonicalJointFrame_slope_scale (d : ℕ) (N : ℕ)
    {L Wsite τ : ℝ} (hL : 1 ≤ L) (hW0 : 0 ≤ Wsite)
    (hW : Wsite ≤ 2 * (d : ℝ) * L) (hτ : 0 < τ) :
    2 * (N : ℝ) / L ≤ canonicalJointFrameWindowConstant d τ *
      (τ * ((N : ℝ) / (8 * (1 + Wsite)))) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hden : 0 < 1 + Wsite := by linarith
  have hc : 1 + Wsite ≤ (2 * (d : ℝ) + 1) * L := by nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * (N : ℝ) by positivity)
  have he : canonicalJointFrameWindowConstant d τ *
      (τ * ((N : ℝ) / (8 * (1 + Wsite)))) =
      2 * (2 * (d : ℝ) + 1) * (N : ℝ) / (1 + Wsite) := by
    unfold canonicalJointFrameWindowConstant
    field_simp [hτ.ne', hden.ne']
    ring
  rw [he]
  apply (div_le_div_iff₀ hLp hden).mpr
  nlinarith

theorem canonicalJointFrame_source_scale {K I : Type*} (d : ℕ) (N : I → ℕ)
    {L Wsite τ : ℝ} (hL : 1 ≤ L) (hW0 : 0 ≤ Wsite)
    (hW : Wsite ≤ 2 * (d : ℝ) * L) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (t : Option K × I) :
    smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant d τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths Wsite τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths Wsite τ N) t : ℤ) : ℝ) := by
  have hK := canonicalJointFrameWindowConstant_two_le d hτ hτ1
  rcases t with ⟨_ | k,i⟩
  · simpa only [smoothPairCoefficientScale, jointFrameSourceHi, jointFrameSourceLo,
      sub_zero, Int.cast_natCast] using
      mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (α := ℝ) (N i))
  · have hs := canonicalJointFrame_slope_scale d (N i) hL hW0 hW hτ
    have hw : 0 ≤ trimmedSpatialWidths Wsite τ N (some k,i) := by
      dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
      positivity
    have hc := Int.le_ceil (trimmedSpatialWidths Wsite τ N (some k,i))
    have hlen : trimmedSpatialWidths Wsite τ N (some k,i) ≤
        ((jointFrameSourceHi N (trimmedSpatialWidths Wsite τ N) (some k,i) -
          jointFrameSourceLo (trimmedSpatialWidths Wsite τ N) (some k,i) : ℤ) : ℝ) := by
      dsimp only [jointFrameSourceHi, jointFrameSourceLo]
      push_cast
      linarith
    have hlen' : τ * ((N i : ℝ) / (8 * (1 + Wsite))) ≤
        ((jointFrameSourceHi N (trimmedSpatialWidths Wsite τ N) (some k,i) -
          jointFrameSourceLo (trimmedSpatialWidths Wsite τ N) (some k,i) : ℤ) : ℝ) := by
      simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul] using hlen
    exact hs.trans (mul_le_mul_of_nonneg_left hlen' (by linarith))

theorem canonicalJointFrame_source_geometry {K I : Type*} [Fintype K] [Fintype I]
    (d : ℕ) (N : I → ℕ) {L Wsite τ : ℝ}
    (hL : 1 ≤ L) (hWL : L ≤ Wsite) (hW : Wsite ≤ 2 * (d : ℝ) * L)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hwide : ∀ i, 1 ≤ τ * ((N i : ℝ) / (8 * (1 + Wsite)))) :
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    (∀ t, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant d τ *
        ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t => Finset.Ico (jointFrameSourceLo width t)
        (jointFrameSourceHi N width t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k i, |(jointFrameSourceLo width (some k,i) : ℝ)| ≤ 2 * (N i : ℝ) / L) ∧
    (∀ k i, |(jointFrameSourceHi N width (some k,i) : ℝ)| ≤ 2 * (N i : ℝ) / L) := by
  intro width
  have hW0 : 0 ≤ Wsite := by linarith
  have hwidth : ∀ k i, 1 ≤ width (some k,i) := by
    intro k i
    simpa only [width, trimmedSpatialWidths, centeredSpatialWidths, one_mul] using hwide i
  have hsmall : ∀ k i, 3 * width (some k,i) ≤ (N i : ℝ) / L :=
    canonicalJointFrame_slope_small N hL hWL hτ hτ1
  obtain ⟨hwindow, hlo, hhi⟩ := jointFrameSource_window_bounds N width
    (lt_of_lt_of_le zero_lt_one hL) hwidth hsmall
  refine ⟨canonicalJointFrame_source_scale d N hL hW0 hW hτ hτ1, ?_, hlo, hhi⟩
  simpa only [Int.cast_zero, sub_zero] using hwindow

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndexedComparableScalarParameterBox
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

theorem comparableScalarParameterRadius_bounds {r L : ℝ} (hr : 2 ≤ r) (hL : 1 ≤ L) :
    0 < comparableScalarParameterRadius r L ∧
      r * L ≤ (comparableScalarParameterRadius r L : ℝ) ∧
      (comparableScalarParameterRadius r L : ℝ) ≤ (r + 1) * L := by
  have hceil : r * L ≤ (⌈r * L⌉₊ : ℝ) := Nat.le_ceil _
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ r * L by positivity)
  refine ⟨?_, hceil, ?_⟩
  · have : (0 : ℝ) < comparableScalarParameterRadius r L :=
      (by positivity : 0 < r * L).trans_le hceil
    exact_mod_cast this
  · change (⌈r * L⌉₊ : ℝ) ≤ (r + 1) * L
    nlinarith

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

theorem indexedComparableScalarParameterSite_bounds {d : ℕ} (hd : 2 ≤ d)
    {K : Type*} [Fintype K] (hK : Fintype.card K = d)
    {r L : ℝ} (_hr : 2 ≤ r) (_hL : 1 ≤ L) (P : K → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ r * L) :
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ r * (d : ℝ) * L := by
  refine ⟨Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _), ?_, ?_⟩
  · have hnonempty : Nonempty K := Fintype.card_pos_iff.mp (by omega)
    let j : K := Classical.choice hnonempty
    exact (hlo j).trans (Finset.single_le_sum
      (fun _ _ => Nat.cast_nonneg (α := ℝ) _) (Finset.mem_univ j))
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hhi j)
    simpa only [Finset.sum_const, Finset.card_univ, hK,
      nsmul_eq_mul, mul_left_comm (d : ℝ) r L, mul_assoc] using h

theorem indexedComparableScalarParameterBox_bounds {d : ℕ} (hd : 2 ≤ d)
    {K : Type*} [Fintype K] (hK : Fintype.card K = d)
    {r L : ℝ} (hr : 2 ≤ r) (hL : 1 ≤ L) (P : K → ℕ)
    (hlo : ∀ j, L ≤ (P j : ℝ)) (hhi : ∀ j, (P j : ℝ) ≤ r * L) :
    (∀ j, (0 : ℤ) < (P j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((P j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (P j : ℤ) - 0 ≤ (comparableScalarParameterRadius r L : ℤ)) ∧
    (comparableScalarParameterRadius r L : ℝ) ≤ (r + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((P j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ (∑ j, (P j : ℝ)) ∧ L ≤ (∑ j, (P j : ℝ)) ∧
      (∑ j, (P j : ℝ)) ≤ r * (d : ℝ) * L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrad := comparableScalarParameterRadius_bounds hr hL
  refine ⟨?_, hLp, ?_, ?_, hrad.2.2, by simp, by simpa using (by linarith : (0 : ℝ) ≤ r), ?_,
    indexedComparableScalarParameterSite_bounds hd hK hr hL P hlo hhi⟩
  · intro j
    exact_mod_cast hLp.trans_le (hlo j)
  · simpa only [sub_zero, Int.cast_natCast] using hlo
  · intro j
    have h := (hhi j).trans hrad.2.1
    rw [sub_zero]
    exact_mod_cast h
  · intro j
    rw [Int.cast_natCast, abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hLp]
    exact (div_le_iff₀ hLp).mpr (hhi j)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

theorem unconditionedSpatialWidthCutoff_le_exp {P Q W τ : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hW : W ≤ Real.exp Q)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    unconditionedSpatialWidthCutoff W τ 1 ≤ Real.exp (Q + 2 * P + 16) := by
  have heP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have heQ : 1 ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  have hfour : (4 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h128 : (128 : ℝ) ≤ Real.exp 16 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    have hp' : (128 : ℝ) ≤ Real.exp 7 := by
      norm_num [← Real.exp_nat_mul] at hp
      exact hp
    exact hp'.trans (Real.exp_le_exp.mpr (by norm_num))
  have hmax : max (8 * (probabilityProfileLipschitz : ℝ)) 1 ≤ 8 * Real.exp P :=
    max_le (mul_le_mul_of_nonneg_left hprofile (by norm_num)) (by linarith)
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      4 / τ ≤ Real.exp 16 * Real.exp P := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hfour hτP (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)
      _ = Real.exp (P + 16) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      8 * (1 + W) * max (8 * (probabilityProfileLipschitz : ℝ)) 1 / τ ≤
          8 * (2 * Real.exp Q) * (8 * Real.exp P) * Real.exp P := by
        rw [div_eq_mul_inv]
        gcongr
        linarith
      _ = 128 * Real.exp (Q + 2 * P) := by rw [Real.exp_add, two_mul P, Real.exp_add]; ring
      _ ≤ Real.exp 16 * Real.exp (Q + 2 * P) :=
        mul_le_mul_of_nonneg_right h128 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem canonicalScalarPhysicalSize {X : Type*} (d : ℕ) {P budget W τ : ℝ}
    (hP : 0 ≤ P) (hbudget : 0 ≤ budget)
    (hd : (d : ℝ) ≤ Real.exp P) (hW : W ≤ 2 * d * Real.exp budget)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (N : X → ℕ)
    (hN : ∀ i, Real.exp ((d + 4 : ℝ) * (budget + P + 20)) ≤ (N i : ℝ)) :
    (∀ i, unconditionedSpatialWidthCutoff W τ 1 ≤ (N i : ℝ)) ∧
      ∀ i, Real.exp budget * (Real.exp budget) ^ (d + 1) ≤ 2 * (N i : ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hWexp : W ≤ Real.exp (budget + P + 1) := by
    calc
      W ≤ 2 * d * Real.exp budget := hW
      _ ≤ Real.exp 1 * Real.exp P * Real.exp budget := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcut := unconditionedSpatialWidthCutoff_le_exp hP
    (show 0 ≤ budget + P + 1 by positivity) hWexp hτ hτP hprofile
  constructor
  · intro i
    apply hcut.trans
    apply (Real.exp_le_exp.mpr ?_).trans (hN i)
    nlinarith [mul_nonneg hd0 hbudget, mul_nonneg hd0 hP]
  · intro i
    calc
      _ = Real.exp (((d : ℝ) + 2) * budget) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (((d : ℝ) + 4) * (budget + P + 20)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hd0 hP]
      _ ≤ (N i : ℝ) := hN i
      _ ≤ 2 * (N i : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (N i)]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem indexedComparableScalarGeometryData
    (d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {K I : Type*} [Fintype K] [Fintype I]
    (hK : Fintype.card K = d) {P0 budget σ : ℝ}
    (hP0 : 0 ≤ P0) (hbudget0 : 0 ≤ budget)
    (hDP0 : ((r*d : ℕ) : ℝ) ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hτP0 : (unconditionedSpatialTrimFraction (Fintype.card I) σ)⁻¹ ≤ Real.exp P0)
    (parameters : K → ℕ)
    (hlo : ∀ j, Real.exp budget ≤ (parameters j : ℝ))
    (hhi : ∀ j, (parameters j : ℝ) ≤ (r : ℝ) * Real.exp budget)
    (N : I → ℕ)
    (hN : ∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) :
    IndexedComparableScalarGeometryData d r (Real.exp budget) (∑ j, (parameters j : ℝ))
      (unconditionedSpatialTrimFraction (Fintype.card I) σ) parameters N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
  let L := Real.exp budget
  let W := ∑ j, (parameters j : ℝ)
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).1
  have hτ1 : τ ≤ 1 :=
    ((unconditionedSpatialTrimFraction_bounds (Fintype.card I) hσ hσ1).2.1).trans (by norm_num)
  have hL : 1 ≤ L := Real.one_le_exp_iff.mpr hbudget0
  have hbox := indexedComparableScalarParameterBox_bounds hd hK (by exact_mod_cast hr) hL parameters hlo hhi
  obtain ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft, hright,
    hW0, hWL, hWbound⟩ := hbox
  have hWgeometry : W ≤ 2 * ((r*d : ℕ) : ℝ) * L := by
    have hh : W ≤ ((r*d : ℕ) : ℝ) * L := by
      simpa only [Nat.cast_mul] using hWbound
    have hp : 0 ≤ ((r*d : ℕ) : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hLpos.le
    nlinarith
  have hphysical := canonicalScalarPhysicalSize (r*d) hP0 hbudget0 hDP0
    hWgeometry hτ hτP0 hprofile N hN
  have hdD : d ≤ r*d := by
    have hh := Nat.mul_le_mul_right d hr
    omega
  have hphysicalActual (i : I) : L * L^(d+1) ≤ 2*(N i : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (Nat.add_le_add_right hdD 1)) hLpos.le).trans (hphysical.2 i)
  obtain ⟨_, _, hwidth, hscale, hwide, hmargin, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := K) hW0 hσ hσ1 N hphysical.1
  obtain ⟨hZ, _⟩ := exists_selectedResidue_physical_cap (0 : K → ℤ)
    (fun _ : I => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _)
    (trimmedSpatialWidths W τ N) hwidth hscale
  have hKpos : 0 < Fintype.card K := by omega
  let k₀ : K := Classical.choice (Fintype.card_pos_iff.mp hKpos)
  have hgeometry := canonicalJointFrame_source_geometry (K := K) (r*d) N hL hWL hWgeometry hτ hτ1
    (fun i => by simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul]
      using hwide (some k₀, i))
  have hroot (i : I) : trimmedSpatialWidths (K := K) W τ N (none, i) ≤
      (spatialTrimMargin τ N i : ℝ) := by
    have hceil := Nat.le_ceil (τ * (N i : ℝ) / 4)
    change τ * ((N i : ℝ) / 8) ≤ (⌈τ * (N i : ℝ) / 4⌉₊ : ℝ)
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (α := ℝ) (N i))]
  have hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2 := by
    linarith
  exact {
    hτ := hτ
    hτ1 := hτ1
    hL := hL
    hwidth := hwidth
    hmargin := hmargin
    hZ := hZ
    hparam := hparam
    sourceGeometry := by simpa only [Fintype.mem_piFinset, L, τ] using hgeometry
    hroot := hroot
    hloss := hloss
    hscale := hscale
    physicalSize := hphysicalActual
    parameterBox := ⟨hparam, hLpos, hparSide, hparRadius, hrad, hrelative, hleft,
      hright, hW0, hWL, hWbound⟩ }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarRectangleGeometry
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped Classical
variable {J : Type*} {N : J → ℕ} {q : ℕ}

theorem length_le_parent (S : ResidueBoxSlice N q) (hq : 0 < q) (j : J) :
    S.length j ≤ N j := by
  by_cases hl : 0 < S.length j
  · have hi := S.inside j (S.length j - 1) (by omega)
    have hm : S.length j - 1 ≤ q * (S.length j - 1) := by
      exact Nat.le_mul_of_pos_left _ hq
    omega
  · omega

theorem scalarRectangle_geometry (S : ResidueBoxSlice N q) (hq : 0 < q)
    {L density ratio : ℝ} (hL : 1 ≤ L) (hdensity : 0 < density)
    (hratio : 1 ≤ ratio) (hlong : 4 ≤ density * L)
    (hN : ∀ j, (N j : ℝ) ≤ ratio * L)
    (hlength : ∀ j, density * L / 2 ≤ (S.length j : ℝ)) :
    (∀ j, 2 ≤ S.length j) ∧
    (∀ j, S.length j ≤ ⌈ratio * L⌉₊) ∧
    (⌈ratio * L⌉₊ : ℝ) ≤ (4 * ratio / density) * (density * L / 2) ∧
    (∀ j, |(S.start j : ℝ) / L| ≤ 2 * ratio) ∧
    (∀ j, |((S.start j : ℝ) + (q : ℝ) * S.length j) / L| ≤ 2 * ratio) := by
  have hLpos : 0 < L := by linarith
  have hratio0 : 0 ≤ ratio := by linarith
  have hlen2 (j) : 2 ≤ S.length j := by
    exact_mod_cast (show (2 : ℝ) ≤ S.length j by linarith [hlength j])
  refine ⟨hlen2, ?_, ?_, ?_, ?_⟩
  · intro j
    exact_mod_cast ((Nat.cast_le.mpr (S.length_le_parent hq j) :
      (S.length j : ℝ) ≤ N j).trans (hN j)).trans (Nat.le_ceil _)
  · have hc : (⌈ratio * L⌉₊ : ℝ) ≤ ratio * L + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hratio0 hLpos.le)).le
    have hprod : 1 ≤ ratio * L := one_le_mul_of_one_le_of_one_le hratio hL
    have he : (4 * ratio / density) * (density * L / 2) = 2 * ratio * L := by
      field_simp
      ring
    rw [he]
    linarith
  · intro j
    exact (S.fullSliceRectangle_endpoint_bounds_two hlen2 hLpos hN j).1.trans
      (by linarith)
  · intro j
    exact (S.fullSliceRectangle_endpoint_bounds_two hlen2 hLpos hN j).2

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ComparableScalarSliceParameterBox
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

variable {J : Type*} {P : J → ℕ} {q : ℕ}

theorem comparableScalarSliceParameterBox_bounds (S : ResidueBoxSlice P q) (hq : 0 < q)
    {L density ratio : ℝ} (hL : 1 ≤ L) (hdensity : 0 < density)
    (hratio : 1 ≤ ratio) (hlong : 4 ≤ density * L)
    (hP : ∀ j, (P j : ℝ) ≤ ratio * L)
    (hlen : ∀ j, density * L / 2 ≤ (S.length j : ℝ)) :
    (∀ j, (0 : ℤ) < (S.length j : ℤ)) ∧
    0 < density * L / 2 ∧
    (∀ j, density * L / 2 ≤ (((S.length j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (S.length j : ℤ) - 0 ≤ (⌈ratio * L⌉₊ : ℤ)) ∧
    (⌈ratio * L⌉₊ : ℝ) ≤ (4 * ratio / density) * (density * L / 2) ∧
    (density / 2) * L ≤ density * L / 2 ∧
    (∀ j, |(((S.start j : ℤ) + (q : ℤ) * 0 : ℤ) : ℝ) / L| ≤ 2 * ratio) ∧
    (∀ j, |(((S.start j : ℤ) + (q : ℤ) * (S.length j : ℤ) : ℤ) : ℝ) / L| ≤
      2 * ratio) := by
  obtain ⟨hlen2, hwidth, hwidthRatio, hleft, hright⟩ :=
    S.scalarRectangle_geometry hq hL hdensity hratio hlong hP hlen
  refine ⟨?_, by positivity, ?_, ?_, hwidthRatio, ?_, ?_, ?_⟩
  · intro j
    exact_mod_cast (show 0 < S.length j by have := hlen2 j; omega)
  · intro j
    simpa only [sub_zero, Int.cast_natCast] using hlen j
  · intro j
    simpa only [sub_zero] using (show (S.length j : ℤ) ≤ (⌈ratio * L⌉₊ : ℤ) by
      exact_mod_cast hwidth j)
  · apply le_of_eq
    ring
  · intro j
    simpa only [mul_zero, add_zero, Int.cast_natCast] using hleft j
  · intro j
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hright j

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalUnconditionedScalarTransfer
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_trimmed_scalar_transfer (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (_k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (width : Option J × I → ℝ) (hwidth : ∀ z, 0 < width z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i),
    (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1 / 2 →
    (∀ i, width (none,i) ≤ (margin i : ℝ)) →
    (∀ z : J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some z.1,z.2)) →
    4 * ((Fintype.card (J × I) : ℝ) + 1) ≤ p →
    let sourceLo := jointFrameSourceLo width
    let sourceHi := jointFrameSourceHi N width
    ∀ (origin : Option J × I → ℤ),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E) cellLog meshLog ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (d + 1) ≤ H i) →
    (selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_unconditioned_joint_scalar_transfer_s2.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim sourceLo sourceHi origin
    hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hLexp hHexp
  have hN (i : I) : 0 < N i := by have := hmargin i; omega
  have hsource : ∀ z, sourceLo z < sourceHi z :=
    jointFrameSource_nonempty N hN width (fun z => (hwidth z).le)
  have hframe := jointIntegerFrame_mem_sourceBox N margin (fun i => (hmargin i).le) width hroot
  have hwidthOne (z : J × I) : (1 : ℝ) ≤ width (some z.1,z.2) := by
    have hprofileOne : (1 : ℝ) ≤ (probabilityProfileLipschitz : ℝ) := by
      exact_mod_cast probabilityProfileLipschitz_one_le
    have hz := hscale z
    linarith
  have hframeBudget := jointFrameSource_volume_cap_le_exp N margin hmargin hloss width hwidthOne hpDim
  exact htransfer nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    hbudget hLexp hHexp (trimmedIntegerBox N margin) (trimmedIntegerBox_nonempty N margin hmargin)
    width hwidth hZ hscale hframe hframeBudget

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_trimmed_threshold_transfer (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (_k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (width : Option J × I → ℝ) (hwidth : ∀ z, 0 < width z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i),
    (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1 / 2 →
    (∀ i, width (none,i) ≤ (margin i : ℝ)) →
    (∀ z : J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some z.1,z.2)) →
    4 * ((Fintype.card (J × I) : ℝ) + 1) ≤ p →
    let sourceLo := jointFrameSourceLo width
    let sourceHi := jointFrameSourceHi N width
    ∀ (origin : Option J × I → ℤ),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    scalarInitialThreshold E (Fintype.card (Option J × I)) (Fintype.card I)
      (Fintype.card J) epsilon p P0 ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (Fintype.card J + 1) ≤ H i) →
    (selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_unconditioned_trimmed_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim sourceLo sourceHi origin
    hwinScale hW hsourceLo hsourceHi
    hbudget hLexp hHexp
  exact htransfer nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim
    origin hwinScale hW hsourceLo hsourceHi hbudget hLexp hHexp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparableScalarPhysicalFamilyPatch
namespace OAI

section

namespace Erdos3

theorem comparableScalarSlice_early_room (d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {p P0 : ℝ} (hp : 2 ≤ p)
    (hP0 : 3 * (8 * (((r * d : ℕ) : ℝ) + 1) * (p + 1)) + 10 ≤ P0) :
    p + 4 * (r : ℝ) + 4 ≤ P0 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrd : (r : ℝ) ≤ ((r * d : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    nlinarith
  have hm : 0 ≤ (((r * d : ℕ) : ℝ) - r) * (p + 1) :=
    mul_nonneg (sub_nonneg.mpr hrd) (by linarith)
  nlinarith

theorem comparableScalarSlice_extra_caps (r : ℕ)
    {p P0 density : ℝ} (hp : 0 ≤ p) (hdensity : 0 < density)
    (hinv : density⁻¹ ≤ Real.exp p) (hroom : p + 4 * (r : ℝ) + 4 ≤ P0) :
    2 * (r : ℝ) ≤ Real.exp P0 ∧
    (density / 2)⁻¹ ≤ Real.exp P0 ∧
    4 * (r : ℝ) / density ≤ Real.exp P0 ∧
    (⌈2 / density⌉₊ : ℝ) ≤ Real.exp P0 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hone : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hcap : 4 * Real.exp p ≤ Real.exp P0 := by
    calc
      _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right h4 (Real.exp_pos p).le
      _ = Real.exp (4 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (show 2 * (r : ℝ) ≤ Real.exp (2 * r) by
      linarith [Real.add_one_le_exp (2 * (r : ℝ))]).trans
    exact Real.exp_le_exp.mpr (by linarith)
  · have he : (density / 2)⁻¹ = 2 * density⁻¹ := by field_simp
    rw [he]
    exact (mul_le_mul_of_nonneg_left hinv (by norm_num)).trans
      ((by nlinarith [Real.exp_pos p] : 2 * Real.exp p ≤ 4 * Real.exp p).trans hcap)
  · rw [div_eq_mul_inv]
    calc
      _ ≤ (4 * (r : ℝ)) * Real.exp p := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ Real.exp (4 * r) * Real.exp p := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 * (r : ℝ))]) (Real.exp_pos p).le
      _ = Real.exp (4 * r + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 / density by positivity)).le
    rw [div_eq_mul_inv] at hceil
    have hx := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    exact (show (⌈2 / density⌉₊ : ℝ) ≤ 4 * Real.exp p by
      simpa only [div_eq_mul_inv] using (show (⌈2 * density⁻¹⌉₊ : ℝ) ≤ 4 * Real.exp p by
        linarith)).trans hcap

theorem comparableScalarSlice_long_scale {p budget density : ℝ}
    (hdensity : Real.exp (-p) ≤ density) (hbudget : p + 4 ≤ budget) :
    4 ≤ density * Real.exp budget := by
  have hpos : 0 < density := (Real.exp_pos (-p)).trans_le hdensity
  calc
    4 ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = Real.exp (-p) * Real.exp (p + 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ density * Real.exp budget := mul_le_mul hdensity (Real.exp_le_exp.mpr hbudget)
      (Real.exp_nonneg _) hpos.le

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section
attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox

theorem exists_indexed_comparableScalarSliceGeometryTransfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ density : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    ((r*d : ℕ) : ℝ) ≤ Real.exp P0 → 2 * (r : ℝ) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < density → (density / 2)⁻¹ ≤ Real.exp P0 →
    4 * (r : ℝ) / density ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant (r*d) τ ≤ Real.exp P0 →
    4 * ((Fintype.card (K × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option K × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : K → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ (q : ℕ) (S : ResidueBoxSlice parameters q),
      0 < q → (q : ℝ) ≤ Real.exp P0 → 4 ≤ density * L →
      (∀ j, density * L / 2 ≤ (S.length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : K, (0 : ℤ) < S.length j),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : K => (0 : ℤ)) (fun j => (S.length j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  let E := Classical.choose (exists_unconditioned_trimmed_threshold_transfer.{u,v,w} s)
  have hE : 2 ≤ E := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v,w} s)).1
  refine ⟨E, hE, ?_⟩
  intro K _ _ hK I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ density
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hDP0 hratioP0 hprofile
    hdensity hdensityP0 hwidthP0 hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget
    g hg L parameters hlo hhi q S hq hqP0 hlong hlength N hN hunit Wsite width margin
  have data := indexedComparableScalarGeometryData d r hd hr hK hP0 hbudget0 hDP0 hprofile hσ hσ1 hτP0
    parameters hlo hhi N hN
  let : Nonempty K := Fintype.card_pos_iff.mp (by omega)
  have hratio : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  obtain ⟨hparam, hparMin, hparSide, hparWidth, hwidthRatio, hrelative, hleft, hright⟩ :=
    S.comparableScalarSliceParameterBox_bounds hq data.hL hdensity hratio hlong hhi hlength
  refine ⟨data.hwidth, data.hmargin, data.hZ, hparam, ?_⟩
  intro h hh hupper
  have hPone : (1 : ℝ) ≤ Real.exp P0 := Real.one_le_exp_iff.mpr hP0
  have hdD : d ≤ r*d := by have hh := Nat.mul_le_mul_right d hr; omega
  have hdP0 : (d : ℝ) ≤ Real.exp P0 :=
    (show (d : ℝ) ≤ ((r*d : ℕ) : ℝ) by exact_mod_cast hdD).trans hDP0
  have hK0 : 0 ≤ canonicalJointFrameWindowConstant (r*d) τ :=
    (by norm_num : (0 : ℝ) ≤ 2).trans
      (canonicalJointFrameWindowConstant_two_le (r*d) data.hτ data.hτ1)
  have htail := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v,w} s)).2 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2
    hnTarget (by simpa only [hK] using hd) (by simpa only [hK] using hdP0) hprofile
    g hg (Classical.choice (inferInstance : Nonempty K)) q (fun j => (S.start j : ℤ)) 0
    (fun j => (S.length j : ℤ)) hparam hq hqP0
    L (2 * (r : ℝ)) 1 1 (canonicalJointFrameWindowConstant (r*d) τ)
    (density / 2) (4 * (r : ℝ) / density)
    (by linarith) (by norm_num) (by norm_num) hK0 (by positivity) (by positivity)
    hratioP0 hPone hPone hKP0 hdensityP0 hwidthP0
    0 N (fun i => 2 * (N i : ℝ)) (fun _ => le_rfl)
    (fun i => by nlinarith only [Nat.cast_nonneg (α := ℝ) (N i)]) hunit h hh hupper
    ⌈(r : ℝ) * L⌉₊ (density * L / 2) hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright width data.hwidth data.hZ margin data.hmargin data.hloss data.hroot
    (fun z => by simpa only [residueProfileWidth, Nat.cast_one, div_one]
      using data.hscale (some z.1,z.2)) hframeDim 0
    data.sourceGeometry.1
    (by simpa only [Fintype.mem_piFinset, Pi.zero_apply, width, Wsite, τ, L]
      using data.sourceGeometry.2.1)
    (fun j i => by simpa only [one_mul] using data.sourceGeometry.2.2.1 j i)
    (fun j i => by simpa only [one_mul] using data.sourceGeometry.2.2.2 j i)
    (by simpa only [hK] using hbudget) le_rfl
    (by simpa only [hK] using data.physicalSize)
  have hdec : (fun a b : K => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq K) := Subsingleton.elim _ _
  rw [hdec] at htail
  exact htail

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

theorem exists_indexed_comparable_unconditioned_scalar_slice_transfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    IndexedComparableUnconditionedScalarSliceTransferStatement.{u,v,w} s d r epsilon := by
  unfold IndexedComparableUnconditionedScalarSliceTransferStatement
  obtain ⟨E, hE, hgeom⟩ := exists_indexed_comparableScalarSliceGeometryTransfer.{u,v,w} s d r hd hr
  obtain ⟨A, C, F, hA, hC, hF, hselect⟩ :=
    exists_comparableScalarSelectedBudget_s2 E d r hE hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro K _ _ hK I V _ _ _ _ _ _ _ d0 nilmanifold p σ level density hp hn hσ hσ1 hσinv hlevel hlevel2 hdensity hdensityInv
    g hg target budget L parameters hlo hhi q S hq hqCap hlength N hN hunit τ Wsite width margin
  let P0 := (A : ℝ) * (target + 1)
  have hsel := hselect (Fintype.card I) hp hn hσ hσinv
  have hpTarget := hsel.1
  have htarget := hsel.2.1
  have hnTarget := hsel.2.2.1
  have hframeDim := hsel.2.2.2.1
  have hP0 := hsel.2.2.2.2.1
  have htargetP0 := hsel.2.2.2.2.2.1
  have hepsP0 := hsel.2.2.2.2.2.2.1
  have hprofile := hsel.2.2.2.2.2.2.2.1
  have hDP0 := hsel.2.2.2.2.2.2.2.2.1
  have hdP0 := hsel.2.2.2.2.2.2.2.2.2.1
  have hrPlusOneP0 := hsel.2.2.2.2.2.2.2.2.2.2.1
  have htwoP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.1
  have hτP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKP0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudget0 := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hthreshold := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNlog := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbudgetFinal := hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hframeDim' : 4 * ((Fintype.card (K × I) : ℝ) + 1) ≤ target := by
    simpa only [Fintype.card_prod, hK, Nat.cast_mul, target] using hframeDim
  have hthreshold' : scalarInitialThreshold E (Fintype.card (Option K × I))
      (Fintype.card I) d epsilon target P0 ≤ budget := by
    have hc : Fintype.card (Option K × I) = (d + 1) * Fintype.card I := by simp [hK]
    rw [hc]
    exact hthreshold
  have hNphysical (i) : Real.exp (((r * d : ℕ) + 4 : ℝ) * (budget + P0 + 20)) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hNlog).trans (hN i)
  have hroom := comparableScalarSlice_early_room d r hd hr hp htargetP0
  obtain ⟨hratioP0, hdensityP0, hwidthP0, hqP0⟩ :=
    comparableScalarSlice_extra_caps r (by linarith : 0 ≤ p) hdensity hdensityInv hroom
  have hdensityLower : Real.exp (-p) ≤ density := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ hdensity (Real.exp_pos p)).mp hdensityInv
  have htBig : p + 4 ≤ target := by
    have hrd : (0 : ℝ) ≤ ((r*d : ℕ) : ℝ) := Nat.cast_nonneg _
    change p + 4 ≤ 8 * (((r*d : ℕ) : ℝ) + 1) * (p + 1)
    nlinarith
  have hpow : target + 2 ≤ budget := by
    change target + 2 ≤ (target + 2) ^ C
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ target + 2) (by omega : 1 ≤ C))
  have hlong : 4 ≤ density * L :=
    comparableScalarSlice_long_scale hdensityLower (htBig.trans (by linarith))
  obtain ⟨hwidth, hmargin, hZ, hparam, htail⟩ :=
    hgeom hK (I := I) (V := V) nilmanifold target epsilon P0 level budget σ density
      htarget hepsilon hepsilon1 hP0 htargetP0 hepsP0
      ((Real.exp_le_exp.mpr (neg_le_neg hpTarget)).trans hlevel)
      hlevel2 hnTarget hDP0 hratioP0 hprofile hdensity hdensityP0 hwidthP0
      hσ hσ1 hτP0 hKP0 hframeDim' hbudget0 hthreshold'
      g (hg.mono hpTarget) parameters hlo hhi q S hq
      ((Nat.cast_le.mpr hqCap).trans hqP0) hlong hlength N hNphysical hunit
  exact ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩

end
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerScalarPassage
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w x
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

theorem exists_indexed_comparable_scalar_shared_slice_tail_s2_oai (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    IndexedComparableScalarSharedSliceTailStatement.{u,v,w,x} s d r epsilon := by
  obtain ⟨A, C, F, hA, hC, hF, htransfer⟩ :=
    exists_indexed_comparable_unconditioned_scalar_slice_transfer.{u,v,x} s d r hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro K _ _ hK I V _ _ _ _ _ _ _ d0 nilmanifold p σ level density hp hn hσ hσ1 hσinv
    hlevel hlevel2 hdensity hdensityInv g hg target budget L parameters hlo hhi
    κ _ _ stride S hq hqCap hlength N hN hunit τ Wsite width margin
  have hfamily (c : κ) := htransfer hK nilmanifold hp hn hσ hσ1 hσinv hlevel hlevel2
    hdensity hdensityInv g hg parameters hlo hhi (stride c) (S c) (hq c) (hqCap c)
    (hlength c) N hN hunit
  choose hwidth hmargin hZ hparam hbudget htail using hfamily
  let c0 : κ := Classical.choice inferInstance
  refine ⟨hwidth c0, hmargin c0, hZ c0, hparam, hbudget c0, ?_⟩
  intro c h hh hnoincrement
  exact htail c h hh hnoincrement

end
end Erdos3

end

end OAI
end

theorem solution.{u, v, w, x} : type_of% @OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail_s2_oai.{u, v, w, x} := @OAI.Erdos3.exists_indexed_comparable_scalar_shared_slice_tail_s2_oai.{u, v, w, x}
