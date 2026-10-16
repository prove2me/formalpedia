-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_choices
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T02:04:23.795004+00:00
-- url     : https://prove2.me/submissions/c32ea2be-f4f0-4ce2-a513-c48a7c3ea9ae

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B1376

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem twoTermErrorChoices_spec {T A B ε : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < twoTermErrorResolution T A ε ∧ T ≤ twoTermErrorResolution T A ε ∧
    0 < twoTermErrorWidth B ε ∧ twoTermErrorWidth B ε ≤ 1 ∧
    A/twoTermErrorResolution T A ε+B*twoTermErrorWidth B ε ≤ ε := by
  let ρ := twoTermErrorResolution T A ε
  let ξ := twoTermErrorWidth B ε
  have hρ : 0 < ρ := by dsimp [ρ, twoTermErrorResolution]; positivity
  have hcut : 2*A/ε ≤ ρ := by
    dsimp [ρ, twoTermErrorResolution]
    linarith
  have hfirst : A/ρ ≤ ε/2 := by
    have hh := (div_le_iff₀ hε).mp hcut
    apply (div_le_iff₀ hρ).mpr
    nlinarith
  have hden : 0 < 2*(1+B) := by positivity
  have hξ : 0 < ξ := lt_min zero_lt_one (div_pos hε hden)
  have hsecond : B*ξ ≤ ε/2 := by
    calc
      _ ≤ B*(ε/(2*(1+B))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
      _ ≤ ε/2 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).mpr
        nlinarith
  refine ⟨hρ, ?_, hξ, min_le_left _ _, by linarith⟩
  have hnonneg : 0 ≤ 2*A/ε := by positivity
  dsimp [twoTermErrorResolution]
  linarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

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

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTupleErrorBudget
namespace OAI

section

namespace Erdos3

theorem spatialTupleErrorChoices (n : ℕ) {G V B ε : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hB : 0 ≤ B) (hε : 0 < ε) :
    let t := spatialTupleTolerance n G V ε
    let ξ := twoTermErrorWidth B t
    0 < ξ ∧ ξ ≤ 1 ∧
    ∀ {A K T Q D : ℝ}, 0 ≤ A → 0 ≤ K → 0 ≤ T → 0 ≤ Q → 0 ≤ D →
      let δ := twoTermErrorWidth K t
      let mesh := δ / 4
      let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧ T ≤ ρ ∧ D ≤ δ * ρ ∧ Q / ρ ≤ ε ∧
      ∀ {g v : ℝ}, 0 ≤ g → g ≤ G → 0 ≤ v → v ≤ V →
        let e := A / ρ + B * ξ + K * δ
        n * (e + 4 * K * mesh) * (1 + g + e) ^ n * v ≤ ε := by
  intro t ξ
  have ht := spatialTupleTolerance_spec n hG hV hε
  have ht0 : 0 < t := ht.1
  have hξ := twoTermErrorWidth_spec hB ht.1
  have hξ0 : 0 < ξ := hξ.1
  refine ⟨hξ.1, hξ.2.1, ?_⟩
  intro A K T Q D hA hK hT hQ hD δ mesh ρ
  have hδ := twoTermErrorWidth_spec hK ht.1
  have hδ0 : 0 < δ := hδ.1
  have hmesh0 : 0 < mesh := div_pos hδ0 (by norm_num)
  have hbase := twoTermErrorChoices_spec hT hA hB ht.1
  have hQε : 0 ≤ Q / ε := div_nonneg hQ hε.le
  have hDδ : 0 ≤ D / δ := div_nonneg hD hδ.1.le
  have hρbase : twoTermErrorResolution T A t ≤ ρ := by
    dsimp [ρ]
    linarith
  have hρ : 0 < ρ := hbase.1.trans_le hρbase
  have hmove : D ≤ δ * ρ := by
    have hdiv : D / δ ≤ ρ := by dsimp [ρ]; linarith [hbase.1]
    have h := (div_le_iff₀ hδ.1).mp hdiv
    nlinarith
  have hquad : Q / ρ ≤ ε := by
    have hdiv : Q / ε ≤ ρ := by dsimp [ρ]; linarith [hbase.1]
    have h := (div_le_iff₀ hε).mp hdiv
    apply (div_le_iff₀ hρ).mpr
    nlinarith
  refine ⟨hδ.1, hδ.2.1, div_pos hδ.1 (by norm_num), hρ,
    hbase.2.1.trans hρbase, hmove, hquad, ?_⟩
  intro g v hg hgG hv hvV e
  have hpair : A / ρ + B * ξ ≤ t :=
    (add_le_add (div_le_div_of_nonneg_left hA hbase.1 hρbase) le_rfl).trans hbase.2.2.2.2
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by dsimp [e]; linarith [hδ.2.2, ht.2.1]
  have hinner : e + 4 * K * mesh ≤ 2 * t := by
    dsimp [e, mesh]
    linarith [hδ.2.2]
  have hpower : (1 + g + e) ^ n ≤ (2 + G) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ n * (2 * t) * (2 + G) ^ n * V := by gcongr
    _ = 2 * t * (2 + G) ^ n * (n * V) := by ring
    _ ≤ 2 * t * (2 + G) ^ n * ((n + 1) * (1 + V)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    _ = t * (2 * (n + 1) * (2 + G) ^ n * (1 + V)) := by ring
    _ ≤ ε := ht.2.2

end Erdos3

end

section

namespace Erdos3

theorem spatialTupleLateParameters_bound {A K T Q D t ε P : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (ht : 0 < t) (hε : 0 < ε) (hP : 0 ≤ P)
    (hAP : A ≤ Real.exp P) (hKP : K ≤ Real.exp P) (hTP : T ≤ Real.exp P)
    (hQP : Q ≤ Real.exp P) (hDP : D ≤ Real.exp P)
    (htP : t⁻¹ ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    let δ := twoTermErrorWidth K t
    let mesh := δ / 4
    let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
    δ⁻¹ ≤ Real.exp (3 * P + 8) ∧ mesh⁻¹ ≤ Real.exp (3 * P + 8) ∧
      ρ ≤ Real.exp (3 * P + 8) := by
  intro δ mesh ρ
  obtain ⟨hres, hδ⟩ := twoTermErrorChoices_log_bounds hA hK ht hP hTP hAP hKP htP
  have hδ0 := (twoTermErrorWidth_spec hK ht).1
  have hmesh : mesh⁻¹ ≤ Real.exp (2 * P + 8) := by
    dsimp [mesh]
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 4 * Real.exp (2 * P + 4) := by
        apply mul_le_mul
        · linarith [Real.add_one_le_exp (4 : ℝ)]
        · exact hδ
        · exact inv_nonneg.mpr hδ0.le
        · exact (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hquad : Q / ε ≤ Real.exp (2 * P) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hQP hεP (inv_nonneg.mpr hε.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmove : D / δ ≤ Real.exp (3 * P + 4) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp P * Real.exp (2 * P + 4) :=
        mul_le_mul hDP hδ (inv_nonneg.mpr hδ0.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨hδ.trans (Real.exp_le_exp.mpr (by linarith)),
    hmesh.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  have hres' := hres.trans (Real.exp_le_exp.mpr (show 2 * P + 4 ≤ 3 * P + 4 by linarith))
  have hquad' := hquad.trans (Real.exp_le_exp.mpr (show 2 * P ≤ 3 * P + 4 by linarith))
  calc
    ρ ≤ 3 * Real.exp (3 * P + 4) := by dsimp [ρ]; linarith
    _ ≤ Real.exp 4 * Real.exp (3 * P + 4) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

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

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

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

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedFiberErrorConstant_le_exp (j d : ℕ) {G U V R H b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (_hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hV : V ≤ Real.exp b)
    (hR : R ≤ Real.exp b) (hH : H ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) :
    normalizedFiberErrorConstant j d G U V R H K ≤
      Real.exp ((j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4) + 4) := by
  have hone : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbox : 2 * R + 2 ≤ Real.exp (b + 4) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (Real.exp_pos b).le]
  have htwor : 2 * R ≤ Real.exp (b + 4) := by linarith
  have hmax : max 1 (U * V) ≤ Real.exp (2*b) := by
    apply max_le
    · exact Real.one_le_exp_iff.mpr (by positivity)
    · calc
        _ ≤ Real.exp b * Real.exp b := mul_le_mul hU hV hV0 (Real.exp_pos b).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let F := (j : ℝ)^2 + (j + 4) * b + (j + 2*d) * (b + 4)
  have hfirst : integerFiberErrorConstant j d G U V R K ≤ Real.exp F := by
    unfold integerFiberErrorConstant
    calc
      _ ≤ Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) *
          (Real.exp (b + 4))^d * Real.exp b * Real.exp (2*b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j + 4)*b + d*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith [Nat.cast_nonneg j (α := ℝ), Nat.cast_nonneg d (α := ℝ)])
  have hsecond : (G * (j.factorial * U ^ j) * H * (2*R)^d) *
      ((2*R+2)^(j+d) * K) ≤ Real.exp F := by
    calc
      _ ≤ (Real.exp b * (Real.exp ((j : ℝ)^2) * (Real.exp b)^j) * Real.exp b *
          (Real.exp (b+4))^d) * ((Real.exp (b+4))^(j+d) * Real.exp b) := by
        gcongr
        exact factorial_le_exp_sq j
      _ = Real.exp ((j : ℝ)^2 + (j+3)*b + (j+2*d)*(b+4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        simp only [← Real.exp_add]
        push_cast
        congr 1
        ring
      _ ≤ Real.exp F := Real.exp_le_exp.mpr (by dsimp [F]; nlinarith)
  change 2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2*R)^d) * ((2*R+2)^(j+d) * K) ≤ _
  calc
    _ ≤ 4 * Real.exp F := by linarith
    _ ≤ Real.exp F * Real.exp 4 := by nlinarith [Real.exp_pos F]
    _ = _ := by rw [← Real.exp_add]

theorem coefficientComparisonConstant_le_exp (j d : ℕ) {G U V R H C b : ℝ} (K : ℝ≥0)
    (hb : 0 ≤ b) (hG0 : 0 ≤ G) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H)
    (hC0 : 0 ≤ C) (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hV : V ≤ Real.exp b)
    (hR : R ≤ Real.exp b) (hH : H ≤ Real.exp b) (hK : (K : ℝ) ≤ Real.exp b) (hC : C ≤ Real.exp b) :
    normalizedFiberErrorConstant j d G U V R H K * (j.factorial * C^j) ≤
      Real.exp (2*(j : ℝ)^2 + (2*j+4)*b + (j+2*d)*(b+4) + 4) := by
  have he := normalizedFiberErrorConstant_le_exp j d K hb hG0 hU0 hV0 hR0 hH0 hG hU hV hR hH hK
  have hd : (j.factorial : ℝ) * C^j ≤ Real.exp ((j : ℝ)^2 + j*b) := by
    calc
      _ ≤ Real.exp ((j : ℝ)^2) * (Real.exp b)^j := by gcongr; exact factorial_le_exp_sq j
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  calc
    _ ≤ Real.exp ((j : ℝ)^2 + (j+4)*b + (j+2*d)*(b+4) + 4) *
        Real.exp ((j : ℝ)^2 + j*b) := mul_le_mul he hd (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDiscretizationCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) :
    0 ≤ smoothSpatialDiscretizationCost N s M L := by
  unfold smoothSpatialDiscretizationCost normalizedFiberErrorConstant integerFiberErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDiscretizationCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M L : ℕ} {p l : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) (hL : (L : ℝ) ≤ Real.exp l) :
    smoothSpatialDiscretizationCost N s M L ≤
      Real.exp (spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p l) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, hV, hK⟩ := spatialProfileLog_bounds N s hp hM
  have hP : 0 ≤ P := spatialProfileLog_nonneg j d hp
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hc := coefficientComparisonConstant_le_exp j d
    ((d+j)*probabilityProfileLipschitz) hP
    (by unfold scalarSpatialIndexAllowance; positivity)
    (by unfold scalarSpatialInverseAllowance; positivity)
    (Nat.cast_nonneg d) zero_le_one zero_le_one zero_le_one
    hG hU hV hone hone (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hK) hone
  simp only [one_pow, mul_one] at hc
  unfold smoothSpatialDiscretizationCost
  calc
    _ ≤ Real.exp (2*(j : ℝ)^2+(2*j+4)*P+(j+2*d)*(P+4)+4) * (Real.exp l)^j :=
      mul_le_mul hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hL j) (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; rfl

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_residue_scale {K X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) :
    (fun k => residueProfileWidth modulus (trimmedSpatialWidths (K := K) B τ N) (k, x)) =
      physicalSpatialInputScale K (trimmedSpatialRootScale τ N modulus x)
        (trimmedSpatialSlopeScale B τ N modulus x) := by
  funext k
  cases k <;> simp only [residueProfileWidth, trimmedSpatialWidths, centeredSpatialWidths,
    physicalSpatialInputScale, Option.elim', trimmedSpatialRootScale, trimmedSpatialSlopeScale, one_mul] <;> ring

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_residue_width_lower {K X : Type*} {W τ ρ : ℝ}
    (hW : 0 ≤ W) (hρ : 0 ≤ ρ) (N q : X → ℕ) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ τ * (N x : ℝ))
    (z : Option K × X) :
    ρ ≤ residueProfileWidth q (trimmedSpatialWidths W τ N) z := by
  have h := trimmedSpatial_scale_lower hW hρ N q z.2 (hq z.2) (hsize z.2)
  have he := congrFun (trimmedSpatial_residue_scale (K := K) W τ N q z.2) z.1
  rw [he]
  cases z.1
  · exact h.1
  · exact h.2

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

variable [DecidableEq α] [DecidableEq G]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatialError_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) {κ C ρ ξ : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) :
    0 ≤ anisotropicSpatialError s N B κ C ρ ξ := by
  unfold anisotropicSpatialError normalizedFiberErrorConstant integerFiberErrorConstant
    anisotropicSpatialDetAllowance physicalSpatialInverseBound spatialKernelErrorConstant
  positivity

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
variable (p : FiniteProbabilityWeights Ω) (label : Ω → R)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatial_residue_width_lower {G J X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ))
    (z : Option (G ⊕ J) × X) :
    ρ ≤ residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  apply (trimmedSpatial_residue_width_lower hW hρ N q hq hsize z).trans
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
variable (N : X → ℕ) (hN : ∀ x, 0 < N x)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))

variable {dim : ℕ} (root : G ⊕ J → ℤ) (dirs : Matrix (Fin dim) (G ⊕ J) ℤ)
variable (hsite : ∀ s : Finset (Fin dim), (∑ k, |(integerAffineCube root dirs s k : ℝ)|) ≤ W)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (hy : (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).weight y ≠ 0)

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hbudget : allocatedPhysicalRootBudget B U b S c ≤ W)
variable (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnisotropicTupleErrorChoice
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem anisotropicSpatialDiscretizationCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ anisotropicSpatialDiscretizationCost N s M C :=
  mul_nonneg (smoothSpatialDiscretizationCost_nonneg N s M 1) (pow_nonneg hC _)

theorem anisotropicSpatialError_decomposition {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) (C ρ ξ : ℝ) :
    anisotropicSpatialError s N M (1 / (M : ℝ)) C ρ ξ =
      anisotropicSpatialDiscretizationCost N s M C / ρ +
        smoothSpatialDisplacementCost N s M * ξ := by
  unfold anisotropicSpatialError
  rw [physicalSpatialInverseBound_eq_scalar]
  unfold anisotropicSpatialDiscretizationCost smoothSpatialDiscretizationCost
    smoothSpatialDisplacementCost anisotropicSpatialDetAllowance scalarSpatialIndexAllowance
  simp only [Nat.cast_one, one_pow, mul_one]
  ring

theorem anisotropicSpatialDiscretizationCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {C p l : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) (hC : 0 ≤ C) (hCl : C ≤ Real.exp l) :
    anisotropicSpatialDiscretizationCost N s M C ≤
      Real.exp (spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p l) := by
  have hb := smoothSpatialDiscretizationCost_le_exp N s hp hM
    (show ((1 : ℕ) : ℝ) ≤ Real.exp 0 by simp)
  unfold anisotropicSpatialDiscretizationCost
  calc
    _ ≤ Real.exp (spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p 0) *
        (Real.exp l) ^ Fintype.card (Unit ⊕ I) :=
      mul_le_mul hb (pow_le_pow_left₀ hC hCl _) (pow_nonneg hC _) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold spatialDiscretizationLog
      ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem coarseReferenceMassConstant_exp_bound (q : ℕ) (X : Type*) [Fintype X]
    {P D W L : ℝ} (hP : 0 ≤ P) (hq : ((q + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    coarseReferenceMassConstant q X W L ≤ Real.exp (coefficientErrorVolumeLog P + 4) := by
  have h := referenceErrorVolumeFactor_exp_bound q X hP hq hX hL hW hD hWL
  have hprofile0 := smoothProbabilityProfile_pos_zero
  unfold coarseReferenceMassConstant
  rw [mul_assoc]
  calc
    _ ≤ Real.exp 4 * Real.exp (coefficientErrorVolumeLog P) := mul_le_mul
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) h (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AnisotropicTupleChoiceBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem anisotropicTupleEarlyWidth_inv_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] (q : ℕ) (s : Fin q ↪ G)
    {M : ℕ} {p E ε : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hMp : (M : ℝ) ≤ Real.exp p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) :
    let t := spatialTupleTolerance (Fintype.card X)
      (Real.exp (p ^ 3 + anisotropicSpatialCapLog p)) (Real.exp (coefficientErrorVolumeLog p + 4)) ε
    let ξ := twoTermErrorWidth (smoothSpatialDisplacementCost N s M) t
    let Q := anisotropicTupleEarlyBudget N s p E
    ξ⁻¹ ≤ Real.exp (2 * (Q + spatialTupleToleranceLog Q) + 4) := by
  have h := anisotropicTupleEarlyBudget_bounds N s hp hE
  exact spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    (smoothSpatialDisplacementCost_nonneg N s M) hε h.1 (hX.trans h.2.1)
    (Real.exp_le_exp.mpr h.2.2.1) (Real.exp_le_exp.mpr h.2.2.2.1)
    ((smoothSpatialDisplacementCost_le_exp N s hp hMp).trans (Real.exp_le_exp.mpr h.2.2.2.2.1))
    (hεE.trans (Real.exp_le_exp.mpr h.2.2.2.2.2))

theorem spatialPeriodDensityCap_le_exp {G : Type*} [Fintype G] (q : ℕ) (s : Fin q ↪ G)
    {m M period : ℕ} {p : ℝ} (hp : 0 ≤ p) (hM : 0 < M)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hperiod : period ≤ M ^ (m + 1)) :
    (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap s (1 / (M : ℝ)) ≤
        Real.exp (p ^ 3 + anisotropicSpatialCapLog p) := by
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hper := coefficientErrorPeriod_exp_sq hp hm hMp hperiod
  have hΓ : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) ≤ Real.exp (p ^ 3) := by
    have h := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg period) hper (sq_nonneg p) _ hj
    exact h.trans_eq (congrArg Real.exp (by ring))
  have hcap := anisotropicSpatialDensityCap_exp_bound s hp hM hMp hj hG
  have hcap0 := anisotropicSpatialDensityCap_nonneg s (by positivity : 0 ≤ 1 / (M : ℝ))
  calc
    _ ≤ Real.exp (p ^ 3) * Real.exp (anisotropicSpatialCapLog p) := by gcongr
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type*) [Fintype X]


variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem allocatedTupleSpatialError_mono_mesh {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    {Czero rho xi W delta mesh small : ℝ}
    (hC : 0 ≤ Czero) (hρ : 0 ≤ rho) (hξ : 0 ≤ xi) (hW : 0 ≤ W)
    (hδ : 0 ≤ delta) (hmesh : small ≤ mesh) :
    allocatedTupleSpatialError n selection N M period Czero rho xi W delta small ≤
      allocatedTupleSpatialError n selection N M period Czero rho xi W delta mesh := by
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hE := anisotropicSpatialError_nonneg selection N M hκ hC hρ hξ
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  unfold allocatedTupleSpatialError
  dsimp only
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left hmesh (by positivity)
    · positivity
  · positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type*) [Fintype X]


variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (L₀ : ℕ) (hS : S = selectedLayerSamplerScale B U b R σ hR hσ L₀)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
variable (c : ∀ j, U j)
variable (hc : coefficientConstantCenter U center =
  -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
    (constantCoefficientArray U (fun s => c s.1))))
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedAnisotropicTupleChoices
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem boundedAnisotropicSpatialTuple_error_choices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] (q : ℕ) (s : Fin q ↪ G)
    {m M : ℕ} (hM : 0 < M) {p E ε : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) :
    let Csp := Real.exp (p ^ 3 + anisotropicSpatialCapLog p)
    let Vsp := Real.exp (coefficientErrorVolumeLog p + 4)
    let B := smoothSpatialDisplacementCost N s M
    let t := spatialTupleTolerance (Fintype.card X) Csp Vsp ε
    let ξ := twoTermErrorWidth B t
    let Qearly := anisotropicTupleEarlyBudget N s p E
    0 < ξ ∧ ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (2 * (Qearly + spatialTupleToleranceLog Qearly) + 4) ∧
    ∀ {C₀ W L Cg Centry growth : ℝ}, 0 ≤ C₀ → 0 ≤ W → 1 ≤ L →
      0 ≤ Cg → 0 ≤ Centry → growth ≤ Real.exp p → W ≤ growth * L →
      let K := Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W))
      let A := anisotropicSpatialDiscretizationCost N s M C₀
      let T := anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry)
      let Q := Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X))
      let D := Fintype.card N * (2 * Centry)
      let δ := twoTermErrorWidth K t
      let mesh := δ / 4
      let ρ := twoTermErrorResolution T A t + Q / ε + D / δ
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤ ε ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          let Γ := (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q)
          let Kp := Γ * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W))
          let E₁ := anisotropicSpatialError s N M (1 / (M : ℝ)) C₀ ρ ξ + Kp * δ
          Fintype.card X * (E₁ + 4 * Kp * mesh) *
            (1 + Γ * anisotropicSpatialDensityCap s (1 / (M : ℝ)) + E₁) ^ Fintype.card X *
              coarseReferenceMassConstant q X W L ≤ ε := by
  intro Csp Vsp B t ξ Qearly
  have hB : 0 ≤ B := smoothSpatialDisplacementCost_nonneg N s M
  have hc := spatialTupleErrorChoices (Fintype.card X) (G := Csp) (V := Vsp)
    (Real.exp_nonneg _) (Real.exp_nonneg _) hB hε
  have hξ : 0 < ξ := hc.1
  refine ⟨hξ, hc.2.1,
    anisotropicTupleEarlyWidth_inv_bound (N := N) (X := X) q s hp hE hMp hX hε hεE, ?_⟩
  intro C₀ W L Cg Centry growth hC₀ hW hL hCg hCentry hgrowth hWL K A T Q D δ mesh ρ
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hlip0 := anisotropicSpatialDensityLip_nonneg s hκ
  have hA : 0 ≤ A := anisotropicSpatialDiscretizationCost_nonneg N s M hC₀
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmesh0 : 0 ≤ anisotropicSpatialMeshThreshold s N C₀ := by
    unfold anisotropicSpatialMeshThreshold anisotropicSpatialDetAllowance
    positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hδ, hδ1, hmesh, hρ, hTρ, hmove, hquad, hsite⟩ :=
    hc.2.2 (A := A) (K := K) (T := T) (Q := Q) (D := D) hA hK hT hQ hD
  have hshift0 : 0 ≤ 2 * (Fintype.card (Option (G ⊕ N)) : ℝ) * (2 * Centry) := by positivity
  have hprofile0 : 0 ≤ (probabilityProfileLipschitz : ℝ) := NNReal.coe_nonneg _
  have hthreshold : anisotropicSpatialMeshThreshold s N C₀ ≤ T := by dsimp [T]; linarith
  have hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ T := by dsimp [T]; linarith
  have hshift : 2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ T := by dsimp [T]; linarith
  have hquad' : Cg *
      (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤ ε := by
    calc
      _ = Q / ρ := by dsimp only [Q]; ring
      _ ≤ ε := hquad
  refine ⟨hδ, hδ1, hmesh, hρ, hthreshold.trans hTρ, hprofile.trans hTρ,
    hshift.trans hTρ, hmove, hquad', ?_⟩
  intro period hperiod Γ Kp E₁
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hper := coefficientErrorPeriod_exp_sq hp hm hMp hperiod
  have hΓ : Γ ≤ Real.exp (p ^ 3) := by
    have h := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg period) hper (sq_nonneg p) _ hj
    exact h.trans_eq (congrArg Real.exp (by ring))
  have hKp : Kp ≤ K := mul_le_mul_of_nonneg_right hΓ (by positivity)
  have hKp0 : 0 ≤ Kp := by dsimp [Kp, Γ]; positivity
  have hcap := spatialPeriodDensityCap_le_exp q s hp hM hm hq hG hMp hperiod
  have hmass := coarseReferenceMassConstant_exp_bound q X hp hq hX hL hW hgrowth hWL
  have hmass0 : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  have hcap0 := anisotropicSpatialDensityCap_nonneg s hκ
  have hactualCap0 : 0 ≤ Γ * anisotropicSpatialDensityCap s (1 / (M : ℝ)) := by
    dsimp [Γ]
    positivity
  have he0 : 0 ≤ E₁ := by
    dsimp only [E₁]
    rw [anisotropicSpatialError_decomposition]
    change 0 ≤ A / ρ + B * ξ + Kp * δ
    positivity
  have he : E₁ ≤ A / ρ + B * ξ + K * δ := by
    dsimp only [E₁]
    rw [anisotropicSpatialError_decomposition]
    change A / ρ + B * ξ + Kp * δ ≤ A / ρ + B * ξ + K * δ
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hKp hδ.le)
  have hresult := hsite hactualCap0 hcap hmass0 hmass
  dsimp only at hresult
  apply le_trans _ hresult
  gcongr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem anisotropicSpatialMeshThreshold_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {C p l : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hCl : C ≤ Real.exp l) :
    anisotropicSpatialMeshThreshold s N C ≤
      Real.exp (anisotropicSpatialMeshLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p l) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let P := spatialProfileLog j d p
  let Q := ((j + d : ℕ) : ℝ) * 4 + P
  have hP : 0 ≤ P := spatialProfileLog_nonneg j d hp
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : ((d + j : ℝ) * probabilityProfileLipschitz) ≤ Real.exp P :=
    (spatialProfileLog_bounds N s (M := 0) hp (by simpa using Real.exp_nonneg p)).2.2.2
  have hfour : (4 : ℝ) ^ (j + d) ≤ Real.exp (((j + d : ℕ) : ℝ) * 4) :=
    pow_le_exp_mul_of_le_exp (by norm_num) (by linarith [Real.add_one_le_exp (4 : ℝ)])
      (by norm_num) (j + d) le_rfl
  have hprod : 4 ^ (j + d) * ((d + j : ℝ) * probabilityProfileLipschitz) ≤ Real.exp Q := by
    calc
      _ ≤ Real.exp (((j + d : ℕ) : ℝ) * 4) * Real.exp P := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hsum := one_add_le_exp_succ hQ hprod
  have hdet : (j.factorial : ℝ) * C ^ j ≤ Real.exp ((j : ℝ) ^ 2 + j * l) := by
    calc
      _ ≤ Real.exp ((j : ℝ) ^ 2) * (Real.exp l) ^ j := by
        gcongr
        exact factorial_le_exp_sq j
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  change 2 * (1 + 4 ^ (j + d) * ((d + j : ℝ) * probabilityProfileLipschitz)) *
    (j.factorial * C ^ j) ≤ _
  calc
    _ ≤ Real.exp 2 * Real.exp (Q + 1) * Real.exp ((j : ℝ) ^ 2 + j * l) := by
      gcongr
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [anisotropicSpatialMeshLog, Q, P]
      push_cast
      ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem normalizedTupleSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (s : Fin q ↪ G)
    (hM : 0 < M) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) :
    let ξ := normalizedTupleNarrowWidth X N s M p E
    let Qearly := anisotropicTupleEarlyBudget N s p (E + 3)
    0 < ξ ∧ ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (2 * (Qearly + spatialTupleToleranceLog Qearly) + 4) ∧
    ∀ {C₀ W L Cg Centry growth : ℝ}, 0 ≤ C₀ → 0 ≤ W → 1 ≤ L →
      0 ≤ Cg → 0 ≤ Centry → growth ≤ Real.exp p → W ≤ growth * L →
      let δ := normalizedTupleRadius X s M p E W
      let mesh := δ / 4
      let ρ := normalizedTupleResolution X N s M p E C₀ W Cg Centry
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare E / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) s N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare E / 2 := by
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεE : (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
    unfold normalizedSpatialShare
    rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    calc
      _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h := boundedAnisotropicSpatialTuple_error_choices (N := N) (X := X) q s hM hp
    (by linarith : 0 ≤ E + 3) hm hq hG hX hMp hε hεE
  simpa only [normalizedTupleNarrowWidth, normalizedTupleTolerance, normalizedTupleRadius,
    normalizedTupleResolution, allocatedTupleSpatialError, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

theorem allocatedTupleSpatialError_mono_width {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    {Czero rho xi small W delta mesh : ℝ}
    (hC : 0 ≤ Czero) (hρ : 0 ≤ rho) (hsmall : 0 ≤ small)
    (hwidth : small ≤ xi) (hW : 0 ≤ W) (hδ : 0 ≤ delta) (hmesh : 0 ≤ mesh) :
    allocatedTupleSpatialError n selection N M period Czero rho small W delta mesh ≤
      allocatedTupleSpatialError n selection N M period Czero rho xi W delta mesh := by
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hE := anisotropicSpatialError_nonneg selection N M hκ hC hρ hsmall
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  have hmono : anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho small ≤
      anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho xi := by
    rw [anisotropicSpatialError_decomposition, anisotropicSpatialError_decomposition]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hwidth (smoothSpatialDisplacementCost_nonneg N selection M))
  have hE' := hE.trans hmono
  unfold allocatedTupleSpatialError
  dsimp only
  gcongr

end Erdos3.VectorPolynomial

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem sharedWidthNormalizedTupleSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (s : Fin q ↪ G)
    (hM : 0 < M) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) {ξ : ℝ}
    (hξ : 0 < ξ) (hξle : ξ ≤ normalizedTupleNarrowWidth X N s M p E) :
    ξ ≤ 1 ∧
    ∀ {C₀ W L Cg Centry growth : ℝ}, 0 ≤ C₀ → 0 ≤ W → 1 ≤ L →
      0 ≤ Cg → 0 ≤ Centry → growth ≤ Real.exp p → W ≤ growth * L →
      let δ := normalizedTupleRadius X s M p E W
      let mesh := δ / 4
      let ρ := normalizedTupleResolution X N s M p E C₀ W Cg Centry
      0 < δ ∧ δ ≤ 1 ∧ 0 < mesh ∧ 0 < ρ ∧
        anisotropicSpatialMeshThreshold s N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare E / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) s N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare E / 2 := by
  obtain ⟨_, hcanonical, _, hchoices⟩ := normalizedTupleSpatialChoices
    (N := N) (X := X) (m := m) s hM hp hE hm hq hG hX hMp
  refine ⟨hξle.trans hcanonical, ?_⟩
  intro C₀ W L Cg Centry growth hC₀ hW hL hCg hCentry hgrowth hWscale δ mesh ρ
  obtain ⟨hδ, hδ1, hmesh, hρ, hthreshold, hprofile, hshift, hmove, hboundary, hsite⟩ :=
    hchoices hC₀ hW hL hCg hCentry hgrowth hWscale
  refine ⟨hδ, hδ1, hmesh, hρ, hthreshold, hprofile, hshift, hmove, hboundary, ?_⟩
  intro period hperiod
  have hmass : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile0 := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  exact (mul_le_mul_of_nonneg_right
    (allocatedTupleSpatialError_mono_width (Fintype.card X) s N M period hC₀ hρ.le
      hξ.le hξle hW hδ.le hmesh.le) hmass).trans (hsite period hperiod)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

section Maps

variable {α β : Type*} [Semiring α] [Semiring β] (f : α →+* β)

end Maps

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedWidthNormalizedTupleSideBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem normalizedTupleLateParameters_bound (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q M : ℕ} (s : Fin q ↪ G)
    {p E l C₀ W Cg Centry : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hM : 0 < M) (hMp : (M : ℝ) ≤ Real.exp p)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hC₀ : 0 ≤ C₀) (hW : 0 ≤ W) (hCentry : 0 ≤ Centry)
    (hC₀l : C₀ ≤ Real.exp l) (hWl : W ≤ Real.exp l) (hCgl : Cg ≤ Real.exp l)
    (hCentryl : Centry ≤ Real.exp l) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l) :
    let P := normalizedTupleLateBudget X N s p E l
    let δ := normalizedTupleRadius X s M p E W
    let mesh := δ / 4
    let ρ := normalizedTupleResolution X N s M p E C₀ W Cg Centry
    δ⁻¹ ≤ Real.exp (3 * P + 8) ∧ mesh⁻¹ ≤ Real.exp (3 * P + 8) ∧
      ρ ≤ Real.exp (3 * P + 8) := by
  intro P δ mesh ρ
  let j := Fintype.card (Unit ⊕ Fin q)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let Alog := spatialDiscretizationLog j d p l
  let Tlog := anisotropicSpatialMeshLog j d p l
  let Klog := p ^ 3 + anisotropicSpatialCapLog p +
    2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p + l + 1
  let tlog := spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3))
  let n₁ : ℝ := Fintype.card (Option (G ⊕ N))
  let n₂ : ℝ := Fintype.card (Option (G ⊕ N) × X)
  let n₃ : ℝ := Fintype.card N
  have hearly := anisotropicTupleEarlyBudget_bounds N s hp (by linarith : 0 ≤ E + 3)
  have hAlog : 0 ≤ Alog := by
    have := spatialProfileLog_nonneg j d hp
    dsimp [Alog, spatialDiscretizationLog]
    positivity
  have hTlog : 0 ≤ Tlog := by
    have := spatialProfileLog_nonneg j d hp
    dsimp [Tlog, anisotropicSpatialMeshLog]
    positivity
  have hKlog : 0 ≤ Klog := by
    have := anisotropicSpatialCapLog_nonneg hp
    have := spatialProfileLog_nonneg j (Fintype.card (UnselectedColumn s)) hp
    dsimp [Klog]
    positivity
  have htlog : 0 ≤ tlog := spatialTupleToleranceLog_nonneg hearly.1
  have hn₁ : 0 ≤ n₁ := Nat.cast_nonneg _
  have hn₂ : 0 ≤ n₂ := Nat.cast_nonneg _
  have hn₃ : 0 ≤ n₃ := Nat.cast_nonneg _
  have hPeq : P = Alog + Tlog + Klog + tlog + E + 3 + 2 * l + n₁ + n₂ + n₃ + 40 := rfl
  have hP : 0 ≤ P := by rw [hPeq]; positivity
  have hAP : Alog ≤ P := by linarith
  have hKP : Klog ≤ P := by linarith
  have htP : tlog ≤ P := by linarith
  have hEP : E + 3 ≤ P := by linarith
  have hTP : Tlog + l + n₁ + 10 ≤ P := by linarith
  have hQP : 2 * l + n₂ + 24 ≤ P := by linarith
  have hDP : l + n₃ + 2 ≤ P := by linarith
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεE : (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
    unfold normalizedSpatialShare
    rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    calc
      _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht : 0 < normalizedTupleTolerance X p E :=
    (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _) hε).1
  have hit : (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp P := by
    have h := spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _)
      (Real.exp_nonneg _) hε hearly.1 (hX.trans hearly.2.1)
      (Real.exp_le_exp.mpr hearly.2.2.1) (Real.exp_le_exp.mpr hearly.2.2.2.1)
      (hεE.trans (Real.exp_le_exp.mpr hearly.2.2.2.2.2))
    exact h.trans (Real.exp_le_exp.mpr htP)
  have hA := (anisotropicSpatialDiscretizationCost_le_exp N s hp hMp hC₀ hC₀l).trans
    (Real.exp_le_exp.mpr hAP)
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hlip0 := anisotropicSpatialDensityLip_nonneg s hκ
  have hK : Real.exp (p ^ 3) * (anisotropicSpatialDensityLip s (1 / (M : ℝ)) * (1 + W)) ≤ Real.exp P := by
    calc
      _ ≤ Real.exp (p ^ 3) *
          (Real.exp (anisotropicSpatialCapLog p + 2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p) *
            Real.exp (l + 1)) := by
        gcongr
        · exact anisotropicSpatialDensityLip_le_exp s hp hM hMp hq hG
        · exact one_add_le_exp_succ hl hWl
      _ = Real.exp Klog := by simp only [← Real.exp_add]; congr 1; dsimp [Klog]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hKP
  have hn₁exp : n₁ ≤ Real.exp n₁ := by linarith [Real.add_one_le_exp n₁]
  have hn₂exp : n₂ ≤ Real.exp n₂ := by linarith [Real.add_one_le_exp n₂]
  have hn₃exp : n₃ ≤ Real.exp n₃ := by linarith [Real.add_one_le_exp n₃]
  have hprof : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp (l + 8) := by
    calc
      _ ≤ Real.exp 8 * Real.exp l := by gcongr; linarith [Real.add_one_le_exp (8 : ℝ)]
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hshift : 2 * n₁ * (2 * Centry) ≤ Real.exp (l + n₁ + 4) := by
    calc
      _ = 4 * n₁ * Centry := by ring
      _ ≤ Real.exp 4 * Real.exp n₁ * Real.exp l := by gcongr; linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hT : anisotropicSpatialMeshThreshold s N C₀ + 8 * probabilityProfileLipschitz +
      2 * n₁ * (2 * Centry) ≤ Real.exp P := by
    have h₁ := (anisotropicSpatialMeshThreshold_le_exp N s hp hC₀ hC₀l).trans
      (Real.exp_le_exp.mpr (show Tlog ≤ Tlog + l + n₁ + 8 by linarith))
    have h₂ := hprof.trans (Real.exp_le_exp.mpr (show l + 8 ≤ Tlog + l + n₁ + 8 by linarith))
    have h₃ := hshift.trans (Real.exp_le_exp.mpr (show l + n₁ + 4 ≤ Tlog + l + n₁ + 8 by linarith))
    calc
      _ ≤ 3 * Real.exp (Tlog + l + n₁ + 8) := by linarith
      _ ≤ Real.exp 2 * Real.exp (Tlog + l + n₁ + 8) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (Tlog + l + n₁ + 10) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hTP
  have hQ : Cg * (24 * probabilityProfileLipschitz * n₂) ≤ Real.exp P := by
    calc
      _ ≤ Real.exp l * (Real.exp 24 * Real.exp l * Real.exp n₂) := by
        gcongr
        linarith [Real.add_one_le_exp (24 : ℝ)]
      _ = Real.exp (2 * l + n₂ + 24) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hQP
  have hD : n₃ * (2 * Centry) ≤ Real.exp P := by
    calc
      _ ≤ Real.exp n₃ * (Real.exp 2 * Real.exp l) := by gcongr; linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp (l + n₃ + 2) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hDP
  exact spatialTupleLateParameters_bound (anisotropicSpatialDiscretizationCost_nonneg N s M hC₀)
    (by positivity) ht hε hP hA hK hT hQ hD hit (hεE.trans (Real.exp_le_exp.mpr hEP))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem spatialSize_of_log_bounds {W q ρ ξ τ N R B l : ℝ}
    (hW : 0 ≤ W) (hq : 0 ≤ q) (hρ : 0 ≤ ρ) (hξ : 0 < ξ) (hτ : 0 < τ) (hl : 0 ≤ l)
    (hWl : W ≤ Real.exp l) (hql : q ≤ Real.exp l) (hρR : ρ ≤ Real.exp R)
    (hξB : ξ⁻¹ ≤ Real.exp B) (hτl : τ⁻¹ ≤ Real.exp l)
    (hN : Real.exp (R + B + 3 * l + 9) ≤ N) :
    8 * (1 + W) * q * ρ ≤ (ξ * τ) * N := by
  have hs : 8 * (1 + W) * q * ρ * ξ⁻¹ * τ⁻¹ ≤ N := by
    calc
      _ ≤ Real.exp 8 * Real.exp (l + 1) * Real.exp l * Real.exp R * Real.exp B * Real.exp l := by
        gcongr
        · linarith [Real.add_one_le_exp (8 : ℝ)]
        · exact one_add_le_exp_succ hl hWl
      _ = Real.exp (R + B + 3 * l + 9) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hN
  have hs' : (8 * (1 + W) * q * ρ) / (ξ * τ) ≤ N := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hs
  simpa only [mul_comm N] using (div_le_iff₀ (mul_pos hξ hτ)).mp hs'

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem sharedWidthNormalizedTupleSpatialSize (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q m M : ℕ} (s : Fin q ↪ G)
    {p E l C₀ W Cg Centry stride ξ Bξ τ side : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hM : 0 < M)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hC₀ : 0 ≤ C₀) (hW : 0 ≤ W) (hCg : 0 ≤ Cg) (hCentry : 0 ≤ Centry)
    (hC₀l : C₀ ≤ Real.exp l) (hWl : W ≤ Real.exp l) (hCgl : Cg ≤ Real.exp l)
    (hCentryl : Centry ≤ Real.exp l) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l)
    (hstride : 0 ≤ stride) (hstridel : stride ≤ Real.exp l) (hτ : 0 < τ) (hτl : τ⁻¹ ≤ Real.exp l)
    (hξ : 0 < ξ) (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (hside : Real.exp (sharedWidthNormalizedTupleSideLog X N s p E l Bξ) ≤ side) :
    8 * (1 + W) * stride * normalizedTupleResolution X N s M p E C₀ W Cg Centry ≤
      (ξ * τ) * side := by
  obtain ⟨_, _, _, hc⟩ := normalizedTupleSpatialChoices (N := N) (X := X)
    (m := m) s hM hp hE hm hq hG hX hMp
  have hρ := (hc (C₀ := C₀) (W := W) (L := 1 + W) (Cg := Cg) (Centry := Centry)
    (growth := 1) hC₀ hW (by linarith) hCg hCentry (Real.one_le_exp hp) (by linarith)).2.2.2.1
  have hq' : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hlate := normalizedTupleLateParameters_bound X N s hp hE hl hM hMp hq' hG hX
    hC₀ hW hCentry hC₀l hWl hCgl hCentryl hprofile
  apply spatialSize_of_log_bounds hW hstride hρ.le hξ hτ hl hWl hstridel hlate.2.2 hξB hτl
  convert hside using 1
  unfold sharedWidthNormalizedTupleSideLog
  congr 1
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProjectedSpatialComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedSpatialLateInputBounds
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (C V : Fin m → ℝ≥0) {P Q W : ℝ} (hP : 0 ≤ P) (hPQ : P ≤ Q)
    (hm : (m : ℝ) ≤ P) (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P) (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) (hW : 0 ≤ W) (hWQ : W ≤ Real.exp Q) :
    let l := allocatedSpatialLateLog (G := G) B P Q
    let C₀ := 1 + (S.value : ℝ) + W
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    0 ≤ l ∧ Q ≤ l ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
      C₀ ≤ Real.exp l ∧ cap ≤ Real.exp l ∧
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l ∧
      W ≤ Real.exp l ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp l := by
  intro l C₀ cap
  have hQ : 0 ≤ Q := hP.trans hPQ
  let caplog := (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) * allocatedAmbientLog m P
  have hcaplog : 0 ≤ caplog := mul_nonneg (Nat.cast_nonneg _) (allocatedAmbientLog_nonneg m hP)
  have hleq : l = 2 * Q + 3 + caplog := rfl
  have hl : 0 ≤ l := by rw [hleq]; positivity
  have hQl : Q ≤ l := by linarith
  have hLQ := hLP.trans (Real.exp_le_exp.mpr hPQ)
  have hcapbase := (allocatedAmbientConstants_exp_bounds B R σ S.value S.positive
    (fun j => Fintype.card (J j)) C V hP hm hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP).1
  have hcap : cap ≤ Real.exp l := by
    calc
      _ ≤ (Real.exp (allocatedAmbientLog m P)) ^ Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
        dsimp [cap]
        gcongr
      _ = Real.exp caplog := by rw [← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hC : C₀ ≤ Real.exp l := by
    have h1 : 1 ≤ Real.exp Q := Real.one_le_exp hQ
    calc
      _ ≤ 3 * Real.exp Q := by dsimp [C₀]; linarith
      _ ≤ Real.exp 2 * Real.exp Q := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (Q + 2) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hvsucc : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1 ≤ Real.exp Q := by
    linarith [Real.add_one_le_exp Q]
  have hentryeq : allocatedPhysicalEntryBudget B U b S (fun _ => 0) =
      1 + ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * S.value := by
    simp [allocatedPhysicalEntryBudget, allocatedPhysicalRootBudget]
    ring
  have hentry : allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l := by
    rw [hentryeq]
    calc
      _ ≤ 1 + Real.exp Q * Real.exp Q := add_le_add le_rfl
        (mul_le_mul hvsucc hLQ (Nat.cast_nonneg _) (Real.exp_pos _).le)
      _ = 1 + Real.exp (2 * Q) := by rw [← Real.exp_add, ← two_mul]
      _ ≤ Real.exp (2 * Q + 1) := one_add_le_exp_succ (by positivity) le_rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  refine ⟨hl, hQl, ?_, ?_, ?_, hC, hcap, hentry,
    hWQ.trans (Real.exp_le_exp.mpr hQl), hAP.trans (Real.exp_le_exp.mpr (hPQ.trans hQl))⟩
  all_goals dsimp [C₀]; linarith [Nat.cast_nonneg (α := ℝ) S.value]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSourceNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.late_bounds {P : ℝ}
    (h : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let l := allocatedSpatialLateLog (G := G) B P P
    let C₀ := 1 + (S.value : ℝ) + W
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    0 ≤ W ∧ 0 ≤ l ∧ P ≤ l ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
      C₀ ≤ Real.exp l ∧ cap ≤ Real.exp l ∧
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l ∧
      W ≤ Real.exp l ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp l := by
  have hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
  exact ⟨hW, allocatedSpatialLateInputBounds B U b S C V h.nonneg le_rfl
    h.degree h.variable_count hR hσ h.radius_inv h.width_inv h.coefficients h.real_axes
    h.integer_axes h.ambient_axes h.profile h.length h.chart h.covolume hW h.root⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uX

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SharedWidthAllocatedCanonicalSpatialNativeSource
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem sharedWidthCanonicalSlicedSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (selection : Fin q ↪ G)
    (hM : 0 < M) {p target : ℝ} (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξle : ξ ≤ normalizedTupleNarrowWidth X N selection M p target) :
    ξ ≤ 1 ∧
    ∀ {C₀ W L Cg Centry growth earlyMesh : ℝ},
      0 ≤ C₀ → 0 ≤ W → 1 ≤ L → 0 ≤ Cg → 0 ≤ Centry →
      growth ≤ Real.exp p → W ≤ growth * L → 0 < earlyMesh →
      let δ := normalizedTupleRadius X selection M p target W
      let ρ := normalizedTupleResolution X N selection M p target C₀ W Cg Centry
      let mesh := min (δ / 4) earlyMesh
      0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧ 0 < mesh ∧
        mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
        anisotropicSpatialMeshThreshold selection N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare target / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) selection N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare target / 2 := by
  obtain ⟨hξ1, hchoices⟩ :=
    sharedWidthNormalizedTupleSpatialChoices (N := N) (X := X) (m := m) selection hM hp htarget
      hm hq hG hX hMp hξ hξle
  refine ⟨hξ1, ?_⟩
  intro C₀ W L Cg Centry growth earlyMesh hC₀ hW hL hCg hCentry hgrowth hWscale hearlyMesh
    δ ρ mesh
  obtain ⟨hδ, hδ1, hmesh₀, hρ, hthreshold, hρ8, hshift, hmove, hboundary, hsite⟩ :=
    hchoices hC₀ hW hL hCg hCentry hgrowth hWscale
  have hfine : mesh ≤ δ / 4 := min_le_left _ _
  refine ⟨hδ, hδ1, hρ, lt_min hmesh₀ hearlyMesh, min_le_right _ _, hfine,
    hthreshold, hρ8, hshift, hmove, hboundary, ?_⟩
  intro period hperiod
  have hmass : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  exact (mul_le_mul_of_nonneg_right
    (allocatedTupleSpatialError_mono_mesh (Fintype.card X) selection N M period
      hC₀ hρ.le hξ.le hW hδ.le hfine) hmass).trans (hsite period hperiod)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.shared_width_canonical_spatial_size
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau ξ Bξ : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hξ : 0 < ξ) (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (stride N : X → ℕ) (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (sharedWidthNormalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau) Bξ) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    ∀ i, 8 * (1 + W) * (stride i : ℝ) * normalizedTupleResolution X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target
      C₀ W (Real.exp Ecap) Centry ≤
        (ξ * τ) * (N i : ℝ) := by
  intro W C₀ Centry i
  obtain ⟨hW, hl₀, _, hC₀, _, _, hC₀l, _, hCentryl, hWl, hprofile⟩ :=
    hnum.late_bounds B U b S C V hR hσ
  let l := allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau
  have hl : 0 ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hQstride, hEtau]
  have hl₀l : allocatedSpatialLateLog (G := G) B P P ≤ l := by
    dsimp [l]; linarith only [hEcap, hQstride, hEtau]
  have hEcapl : Ecap ≤ l := by dsimp [l]; linarith only [hl₀, hQstride, hEtau]
  have hQstridel : Qstride ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hEtau]
  have hEtaul : Etau ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hQstride]
  exact sharedWidthNormalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n))
    (m := m) selection hp htarget hl hM hm hdim hG hX hMp
    (zero_le_one.trans hC₀) hW (Real.exp_pos _).le
    (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0)))
    (hC₀l.trans (Real.exp_le_exp.mpr hl₀l)) (hWl.trans (Real.exp_le_exp.mpr hl₀l))
    (Real.exp_le_exp.mpr hEcapl) (hCentryl.trans (Real.exp_le_exp.mpr hl₀l))
    (hprofile.trans (Real.exp_le_exp.mpr hl₀l)) (Nat.cast_nonneg _)
    ((hstride i).trans (Real.exp_le_exp.mpr hQstridel)) hτ
    (hτinv.trans (Real.exp_le_exp.mpr hEtaul)) hξ hξB (hside i)

theorem AllocatedSourceNumerics.shared_width_canonical_spatial_choices_oai
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau earlyMesh ξ Bξ : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hξ : 0 < ξ)
    (hξle : ξ ≤ normalizedTupleNarrowWidth X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target)
    (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hearlyMesh : 0 < earlyMesh)
    (stride N : X → ℕ) (hstridepos : ∀ i, 0 < stride i)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (sharedWidthNormalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau) Bξ) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    let δ := normalizedTupleRadius X selection M p target W
    let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M p target C₀ W (Real.exp Ecap) Centry
    let mesh := min (δ / 4) earlyMesh
    0 ≤ W ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) ∧
    0 < ξ ∧ ξ ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧
    0 < mesh ∧ mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
    (∀ i, 8 * (1 + W) * (stride i : ℝ) * ρ ≤ (ξ * τ) * (N i : ℝ)) ∧
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ ∧
    8 * probabilityProfileLipschitz ≤ ρ ∧
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) * (2 * Centry)) ≤ ρ ∧
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) * (2 * Centry) ≤ δ * ρ ∧
    Real.exp Ecap * (24 * probabilityProfileLipschitz *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) ≤ normalizedSpatialShare target / 2 ∧
    (∀ period : ℕ, period ≤ M ^ (m + 1) →
      allocatedTupleSpatialError (Fintype.card X) selection
        (PrincipalTupleIndex B (layerSamplerDegree I n)) M period C₀ ρ ξ W δ mesh *
        coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2) ∧
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    (∀ i, 0 < N i) ∧ (∀ z, 0 < widths z) ∧
    ∀ cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
      cells.Nonempty → 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z := by
  intro W C₀ Centry δ ρ mesh
  obtain ⟨hW, _, _, hC₀, hLC, hWC, _⟩ := hnum.late_bounds B U b S C V hR hσ
  have hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero,
      zero_add, le_refl]
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  obtain ⟨hξ1, hchoices⟩ := sharedWidthCanonicalSlicedSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hp htarget hm hdim hG hX hMp hξ hξle
  obtain ⟨hδ, hδ1, hρ, hmesh, hmeshEarly, hmeshFine, hthreshold, hρ8,
    hshift, hmove, hboundary, hsite⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := S.value) (Cg := Real.exp Ecap)
      (Centry := Centry) (growth := Fintype.card (LayerSamplerVariables G I n B))
      (zero_le_one.trans hC₀) hW hL (Real.exp_pos _).le
      (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0)))
      hvars hWscale hearlyMesh
  have hphysical := hnum.shared_width_canonical_spatial_size B U b S C V hR hσ selection hp htarget
    hEcap hQstride hEtau hM hm hdim hG hX hMp hξ hξB stride N hstride hτ hτinv hside
  have hN (i) : 0 < N i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hside i)
  have hwidth := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  refine ⟨hW, hC₀, hLC, hWC, hWscale, hξ, hξ1, hδ, hδ1, hρ,
    hmesh, hmeshEarly, hmeshFine, hphysical, hthreshold, hρ8, ?_, hmove, hboundary, hsite,
    hN, hwidth, ?_⟩
  · simpa only [mul_assoc] using hshift
  · intro cells hcells
    exact (exists_selectedResidue_physical_cap (fun _ : LayerSamplerVariables G I n B => 0)
      stride hstridepos cells hcells _ hwidth (fun z => hρ8.trans
        (narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N stride hN hstridepos
          hphysical z))).choose

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal
attribute [local irreducible] residueRefinedPeriod

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable (period : ℕ) [NeZero period] (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
variable (modulus : ℕ)
variable (hmodulusRefined : modulus = residueRefinedPeriod period stride)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_choices_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_choices_oai.{u_1, u_2, u_3, u_4, u_5}
