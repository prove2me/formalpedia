-- Prove2me | solution 1 for OAI.Solenoidal.ClassicalSolution.relativeEnergy_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:11:25.798192+00:00
-- url     : https://prove2.me/submissions/ebc7c87f-aabb-4a12-8fc3-02026d48bcce

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/EnergyIdentities.lean:L294-L353
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.ClassicalSolution.relativeEnergy_derivative_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Theorems.Thm_OAI_Solenoidal_periodic_integral_divergence_zero_C1
import Theorems.Thm_OAI_Solenoidal_periodic_transport_zero

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem continuous_integrableOn_cell {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : Continuous g) : IntegrableOn g fundamentalCell := by
  apply (hg.integrableOn_Icc (a := (0 : Space)) (b := fun _ => 10)).mono_set
  intro x hx
  constructor
  · intro j
    exact (hx j (Set.mem_univ j)).1
  · intro j
    exact (hx j (Set.mem_univ j)).2.le

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_translation {g : E → F} (hg : Differentiable ℝ g)
    {c : E} (hc : ∀ x, g (x + c) = g x) (v x : E) :
    directional g v (x + c) = directional g v x := by
  have hd := (hg (x + c)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const c)
  have he : (fun y => g (y + c)) = g := funext hc
  have hd' : HasFDerivAt g (fderiv ℝ g (x + c)) x := by simpa only [Function.comp_def, id_eq, he, ContinuousLinearMap.comp_id] using hd
  exact (congrArg (fun L : E →L[ℝ] F => L v) hd'.fderiv).symm

end DirectionalCalculus

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ClassicalRegularity ----
namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem TorusC1.const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) : TorusC1 (fun _ : Space => c) := by
  refine ⟨differentiable_const c, ?_, fun _ _ => rfl⟩
  intro j
  simpa using (continuous_const : Continuous (fun _ : Space => (0 : E)))

theorem TorusC1.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g h : Space → E} (hg : TorusC1 g) (hh : TorusC1 h) : TorusC1 (g - h) := by
  refine ⟨hg.differentiable.sub hh.differentiable, ?_, ?_⟩
  · intro j
    have he (x : Space) : fderiv ℝ (g - h) x (basis j) =
        fderiv ℝ g x (basis j) - fderiv ℝ h x (basis j) := by
      rw [fderiv_sub (hg.differentiable x) (hh.differentiable x)]
      rfl
    simpa only [he] using (hg.continuous_partial j).fun_sub (hh.continuous_partial j)
  · intro x k
    simp only [Pi.sub_apply, hg.periodic, hh.periodic]

theorem scalarPartial_mul {g h : Space → ℝ}
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (x : Space) (j : Fin 3) :
    fderiv ℝ (g * h) x (basis j) =
      g x * fderiv ℝ h x (basis j) + h x * fderiv ℝ g x (basis j) := by
  rw [fderiv_mul (hg x) (hh x)]
  rfl

theorem TorusC1.mul {g h : Space → ℝ} (hg : TorusC1 g) (hh : TorusC1 h) :
    TorusC1 (g * h) := by
  refine ⟨hg.differentiable.mul hh.differentiable, ?_, ?_⟩
  · intro j
    simp only [scalarPartial_mul hg.differentiable hh.differentiable]
    exact (hg.differentiable.continuous.fun_mul (hh.continuous_partial j)).add
      (hh.differentiable.continuous.fun_mul (hg.continuous_partial j))
  · intro x k
    simp only [Pi.mul_apply, hg.periodic, hh.periodic]

theorem TorusC1.sum {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ι → Space → E)
    (hg : ∀ i, TorusC1 (g i)) : TorusC1 (∑ i, g i) := by
  classical
  refine ⟨Differentiable.sum (fun i _ => (hg i).differentiable), ?_, ?_⟩
  · intro j
    have he (x : Space) : fderiv ℝ (∑ i, g i) x (basis j) =
        ∑ i, fderiv ℝ (g i) x (basis j) := by
      rw [fderiv_sum (fun i _ => (hg i).differentiable x), sum_apply]
    simpa only [he] using continuous_finsetSum _ (fun i _ => (hg i).continuous_partial j)
  · intro x k
    simp only [Finset.sum_apply, fun i => (hg i).periodic]

theorem fderiv_component {g : Space → Space} (hg : Differentiable ℝ g)
    (k : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => g y k) x v = fderiv ℝ g x v k := by
  rw [fderiv_pi (φ := fun j y => g y j) (fun j =>
    (differentiable_apply j).fun_comp hg |>.differentiableAt)]
  rfl

theorem TorusC1.component {g : Space → Space} (hg : TorusC1 g) (k : Fin 3) :
    TorusC1 (fun x => g x k) := by
  refine ⟨(differentiable_apply k).fun_comp hg.differentiable, ?_, ?_⟩
  · intro j
    simp only [fderiv_component hg.differentiable]
    exact (continuous_apply k).comp (hg.continuous_partial j)
  · intro x l
    rw [hg.periodic]

theorem periodic_integral_partial_zero_C1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Space → E} (hg : TorusC1 g) (j : Fin 3) :
    (∫ x in fundamentalCell, fderiv ℝ g x (basis j)) = 0 := by
  classical
  have h := periodic_integral_divergence_zero_C1 (fun k => if k = j then g else 0)
    (fun k => by split_ifs <;> first | exact hg | exact TorusC1.const 0)
  have he (k : Fin 3) (x : Space) :
      fderiv ℝ (if k = j then g else 0) x (basis k) =
        if k = j then fderiv ℝ g x (basis j) else 0 := by
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk]
  simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem periodic_integration_by_parts {g h : Space → ℝ}
    (hg : TorusC1 g) (hh : TorusC1 h) (j : Fin 3) :
    (∫ x in fundamentalCell, g x * fderiv ℝ h x (basis j)) =
      -(∫ x in fundamentalCell, h x * fderiv ℝ g x (basis j)) := by
  have hz := periodic_integral_partial_zero_C1 (hg.mul hh) j
  simp only [scalarPartial_mul hg.differentiable hh.differentiable] at hz
  rw [integral_add (f := fun x => g x * fderiv ℝ h x (basis j))
    (g := fun x => h x * fderiv ℝ g x (basis j))
    (continuous_integrableOn_cell (hg.differentiable.continuous.fun_mul (hh.continuous_partial j)))
    (continuous_integrableOn_cell (hh.differentiable.continuous.fun_mul (hg.continuous_partial j)))] at hz
  linarith

theorem cylinder_spatial_slice {E : Type*} [TopologicalSpace E]
    {g : ℝ → Space → E} {T t : ℝ}
    (hg : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T))
    (ht : t ∈ Set.Icc 0 T) : Continuous (g t) := by
  simpa only [Function.comp_def, id_eq] using hg.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, Set.mem_univ x⟩)

theorem spatialPartial_periodic_of_differentiable {u : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hp : SpatiallyPeriodic u) (j : Fin 3) (x : Space) (k : Fin 3 → ℤ) :
    spatialPartial u j t (x + deck k) = spatialPartial u j t x :=
  directional_translation hu (fun y => hp t y k) (basis j) x

theorem ClassicalSolution.spatialC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) : TorusC1 (u t) := by
  refine ⟨h.differentiable_x t ht, ?_, h.spatial_periodic_u t⟩
  intro j
  exact cylinder_spatial_slice (h.continuous_x t ht j) ⟨ht, le_refl t⟩

theorem ClassicalSolution.spatialPartialC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) :
    TorusC1 (spatialPartial u j t) := by
  refine ⟨h.differentiable_xx t ht j, ?_, ?_⟩
  · intro k
    exact cylinder_spatial_slice (h.continuous_xx t ht j k) ⟨ht, le_refl t⟩
  · exact spatialPartial_periodic_of_differentiable (h.differentiable_x t ht)
      h.spatial_periodic_u j

theorem ClassicalSolution.pressureC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) : TorusC1 (p t) := by
  refine ⟨h.differentiable_p t ht, ?_, h.spatial_periodic_p t⟩
  intro j
  exact (continuous_apply j).comp
    (cylinder_spatial_slice (h.continuous_px t ht) ⟨ht, le_refl t⟩)

theorem fderiv_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) (x d : Space) :
    fderiv ℝ g x d = ∑ j : Fin 3, d j • fderiv ℝ g x (basis j) := by
  have hd : d = ∑ j : Fin 3, d j • basis j := by
    ext k
    fin_cases k <;> simp [basis, Fin.sum_univ_succ]
  conv_lhs => rw [hd]
  simp only [map_sum, map_smul]

theorem kineticDensity_continuous : Continuous kineticDensity := by
  unfold kineticDensity
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).fun_mul (continuous_apply i)).div_const 2)

theorem fderiv_kineticDensity {w : Space → Space} (hw : Differentiable ℝ w)
    (x d : Space) :
    fderiv ℝ (fun y => kineticDensity (w y)) x d =
      ∑ i : Fin 3, w x i * (fderiv ℝ w x d) i := by
  have hg (i : Fin 3) : Differentiable ℝ (fun y => w y i) :=
    (differentiable_apply i).fun_comp hw
  have he : (fun y => kineticDensity (w y)) = ∑ i : Fin 3, (fun y => w y i * w y i * (1/2 : ℝ)) := by
    funext y
    simp [kineticDensity, div_eq_mul_inv]
  rw [he, fderiv_sum (fun i _ => (((hg i).fun_mul (hg i)).mul_const (1/2 : ℝ)) x), sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_mul_const (((hg i).fun_mul (hg i)) x), fderiv_fun_mul ((hg i) x) ((hg i) x)]
  simp only [smul_apply, add_apply,
    smul_eq_mul, fderiv_component hw]
  ring

theorem TorusC1.kineticDensity {w : Space → Space} (hw : TorusC1 w) :
    TorusC1 (fun y => kineticDensity (w y)) := by
  have hc (i : Fin 3) := ((hw.component i).mul (hw.component i)).mul (TorusC1.const (1/2 : ℝ))
  convert TorusC1.sum (fun i : Fin 3 => fun y => w y i * w y i * (1/2 : ℝ)) hc using 1
  ext y
  simp [Solenoidal.kineticDensity, div_eq_mul_inv]

theorem periodic_transport_energy_zero {w v : Space → Space}
    (hw : TorusC1 w) (hv : TorusC1 v)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ v x (basis j) j = 0) :
    (∫ x in fundamentalCell, ∑ i : Fin 3, w x i * (fderiv ℝ w x (v x)) i) = 0 := by
  simpa only [fderiv_kineticDensity hw.differentiable] using
    periodic_transport_zero hw.kineticDensity hv hdiv

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.EnergyIdentities ----
namespace OAI

/-! SheetFlows energy identities. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem measurableSet_fundamentalCell : MeasurableSet fundamentalCell :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem continuous_euclidDot {A : Type*} [TopologicalSpace A] {a b : A → Space}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => euclidDot (a x) (b x)) := by
  unfold euclidDot
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp ha).fun_mul ((continuous_apply i).comp hb))

theorem TorusC1.fderiv_along_continuous {w : Space → Space} (hw : TorusC1 w)
    {v : Space → Space} (hv : Continuous v) :
    Continuous (fun x => fderiv ℝ w x (v x)) := by
  have he : (fun x => fderiv ℝ w x (v x)) =
      (fun x => ∑ j : Fin 3, v x j • fderiv ℝ w x (basis j)) :=
    funext (fun x => fderiv_apply_eq_sum w x (v x))
  rw [he]
  exact continuous_finsetSum _ (fun j _ =>
    ((continuous_apply j).comp hv).smul (hw.continuous_partial j))

theorem periodic_pressure_energy_zero {w : Space → Space} {q : Space → ℝ}
    (hw : TorusC1 w) (hq : TorusC1 q)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ w x (basis j) j = 0) :
    (∫ x in fundamentalCell, euclidDot (w x) (fun j => fderiv ℝ q x (basis j))) = 0 := by
  have he (x : Space) : fderiv ℝ q x (w x) =
      euclidDot (w x) (fun j => fderiv ℝ q x (basis j)) := by
    rw [fderiv_apply_eq_sum]
    rfl
  simpa only [he] using periodic_transport_zero hq hw hdiv

theorem periodic_viscous_energy_nonpos {w : Space → Space}
    (hw : TorusC1 w) (hww : ∀ j, TorusC1 (fun x => fderiv ℝ w x (basis j))) :
    (∫ x in fundamentalCell, euclidDot (w x)
      (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j))) ≤ 0 := by
  have hint (j i : Fin 3) : IntegrableOn
      (fun x => w x i * fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j) i)
      fundamentalCell :=
    continuous_integrableOn_cell (((continuous_apply i).comp hw.differentiable.continuous).fun_mul
      ((continuous_apply i).comp ((hww j).continuous_partial j)))
  have hsum (x : Space) : euclidDot (w x)
      (∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j)) =
        ∑ j : Fin 3, ∑ i : Fin 3,
          w x i * fderiv ℝ (fun y => fderiv ℝ w y (basis j)) x (basis j) i := by
    simp only [euclidDot, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint j i))]
  apply Finset.sum_nonpos
  intro j _
  rw [integral_finsetSum _ (fun i _ => hint j i)]
  apply Finset.sum_nonpos
  intro i _
  have hparts := periodic_integration_by_parts (hw.component i) ((hww j).component i) j
  simp only [fderiv_component hw.differentiable,
    fderiv_component (hww j).differentiable] at hparts
  rw [hparts]
  exact neg_nonpos.mpr (integral_nonneg (fun x => mul_self_nonneg _))

theorem stretching_energy_bound {u : Space → Space} (x : Space) (w : Space) {B : ℝ}
    (hB : 0 ≤ B) (hgrad : ∀ j, ‖fderiv ℝ u x (basis j)‖ ≤ B) :
    -euclidDot w (fderiv ℝ u x w) ≤ (6 * B) * kineticDensity w := by
  have hterm (i j : Fin 3) :
      -(w i * (w j * fderiv ℝ u x (basis j) i)) ≤
        B * (w i * w i + w j * w j) / 2 := by
    have hd : |fderiv ℝ u x (basis j) i| ≤ B := by
      exact (norm_le_pi_norm (fderiv ℝ u x (basis j)) i).trans (hgrad j)
    have hww : |w i| * |w j| ≤ (w i * w i + w j * w j) / 2 := by
      nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
    calc
      -(w i * (w j * fderiv ℝ u x (basis j) i)) ≤
          |w i * (w j * fderiv ℝ u x (basis j) i)| := neg_le_abs _
      _ = (|w i| * |w j|) * |fderiv ℝ u x (basis j) i| := by rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ (|w i| * |w j|) * B := mul_le_mul_of_nonneg_left hd (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ ((w i * w i + w j * w j) / 2) * B := mul_le_mul_of_nonneg_right hww hB
      _ = B * (w i * w i + w j * w j) / 2 := by ring
  have he : -euclidDot w (fderiv ℝ u x w) =
      ∑ i : Fin 3, ∑ j : Fin 3, -(w i * (w j * fderiv ℝ u x (basis j) i)) := by
    rw [fderiv_apply_eq_sum]
    simp [euclidDot, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [he]
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, B * (w i * w i + w j * w j) / 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (6 * B) * kineticDensity w := by simp [kineticDensity, Fin.sum_univ_succ]; ring

theorem spatialPartial_sub_at {u v : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hv : Differentiable ℝ (v t)) (j : Fin 3) :
    spatialPartial (v - u) j t = spatialPartial v j t - spatialPartial u j t := by
  funext x
  change fderiv ℝ (v t - u t) x (basis j) = _
  rw [fderiv_sub (hv x) (hu x)]
  rfl

theorem laplacian_sub_at {u v : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hv : Differentiable ℝ (v t))
    (huu : ∀ j, Differentiable ℝ (spatialPartial u j t))
    (hvv : ∀ j, Differentiable ℝ (spatialPartial v j t)) :
    laplacian (v - u) t = laplacian v t - laplacian u t := by
  funext x
  change (∑ j, fderiv ℝ (spatialPartial (v-u) j t) x (basis j)) = _
  simp only [spatialPartial_sub_at hu hv, fderiv_sub (hvv _ x) (huu _ x), sub_apply,
    Finset.sum_sub_distrib]
  rfl

theorem advection_sub_identity {u v : Field} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (hv : Differentiable ℝ (v t)) (x : Space) :
    advection v t x - advection u t x =
      fderiv ℝ (v t - u t) x (v t x) + fderiv ℝ (u t) x (v t x - u t x) := by
  rw [fderiv_sub (hv x) (hu x), map_sub]
  simp only [sub_apply, advection]
  abel

theorem gradient_sub_at {p r : Pressure} {t : ℝ}
    (hp : Differentiable ℝ (p t)) (hr : Differentiable ℝ (r t)) :
    gradient (p-r) t = gradient p t - gradient r t := by
  funext x j
  change fderiv ℝ (p t - r t) x (basis j) = _
  rw [fderiv_sub (hp x) (hr x)]
  rfl

theorem ClassicalSolution.difference_equation {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    timePartial v t x - timePartial u t x =
      -gradient (p-r) t x + ν • laplacian (v-u) t x -
        fderiv ℝ (v t-u t) x (v t x) - fderiv ℝ (u t) x (v t x-u t x) := by
  have hul := hu.differentiable_x t ht
  have hvl := hv.differentiable_x t ht
  have ha := advection_sub_identity hul hvl x
  rw [gradient_sub_at (hv.differentiable_p t ht) (hu.differentiable_p t ht),
    laplacian_sub_at hul hvl (hu.differentiable_xx t ht) (hv.differentiable_xx t ht)]
  rw [eq_sub_of_add_eq (hv.equation t ht x), eq_sub_of_add_eq (hu.equation t ht x)]
  simp only [Pi.sub_apply, smul_sub]
  conv_rhs => rw [sub_sub, ← ha]
  abel

theorem ClassicalSolution.relativeEnergy_derivative_bound
    {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hgrad : ∀ x ∈ fundamentalCell, ∀ j, ‖spatialPartial u j t x‖ ≤ B) :
    (∫ x in fundamentalCell, euclidDot (v t x-u t x)
      (timePartial v t x-timePartial u t x)) ≤ (6*B) * relativeEnergy u v t := by
  let w : Space → Space := v t - u t
  let q : Space → ℝ := p t - r t
  let G : Space → Space := fun x j => fderiv ℝ q x (basis j)
  let L : Space → Space := laplacian (v-u) t
  let A : Space → Space := fun x => fderiv ℝ w x (v t x)
  let C : Space → Space := fun x => fderiv ℝ (u t) x (w x)
  have hw : TorusC1 w := (hv.spatialC1 ht).sub (hu.spatialC1 ht)
  have hq : TorusC1 q := (hv.pressureC1 ht).sub (hu.pressureC1 ht)
  have hww (j : Fin 3) : TorusC1 (fun x => fderiv ℝ w x (basis j)) := by
    change TorusC1 (spatialPartial (v-u) j t)
    rw [spatialPartial_sub_at (hu.differentiable_x t ht) (hv.differentiable_x t ht)]
    exact (hv.spatialPartialC1 ht j).sub (hu.spatialPartialC1 ht j)
  have hdivw (x : Space) : ∑ j : Fin 3, fderiv ℝ w x (basis j) j = 0 := by
    dsimp only [w]
    rw [fderiv_sub (hv.differentiable_x t ht x) (hu.differentiable_x t ht x)]
    simp only [sub_apply, Pi.sub_apply, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hv.incompressible t ht x).trans (hu.incompressible t ht x).symm)
  have hIG : IntegrableOn (fun x => euclidDot (w x) (G x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      (continuous_pi hq.continuous_partial))
  have hIL : IntegrableOn (fun x => euclidDot (w x) (L x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      (continuous_finsetSum _ (fun j _ => (hww j).continuous_partial j)))
  have hIA : IntegrableOn (fun x => euclidDot (w x) (A x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      (hw.fderiv_along_continuous (hv.differentiable_x t ht).continuous))
  have hIC : IntegrableOn (fun x => euclidDot (w x) (C x)) fundamentalCell :=
    continuous_integrableOn_cell (continuous_euclidDot hw.differentiable.continuous
      ((hu.spatialC1 ht).fderiv_along_continuous hw.differentiable.continuous))
  have hg : (∫ x in fundamentalCell, euclidDot (w x) (G x)) = 0 :=
    periodic_pressure_energy_zero hw hq hdivw
  have ha : (∫ x in fundamentalCell, euclidDot (w x) (A x)) = 0 :=
    periodic_transport_energy_zero hw (hv.spatialC1 ht) (hv.incompressible t ht)
  have hl : (∫ x in fundamentalCell, euclidDot (w x) (L x)) ≤ 0 :=
    periodic_viscous_energy_nonpos hw hww
  have he (x : Space) : timePartial v t x-timePartial u t x =
      -G x + ν • L x - A x - C x := hu.difference_equation hv ht x
  have hIE : IntegrableOn (fun x => (6*B) * kineticDensity (w x)) fundamentalCell :=
    (continuous_integrableOn_cell (kineticDensity_continuous.comp hw.differentiable.continuous)).const_mul _
  have hb : -(∫ x in fundamentalCell, euclidDot (w x) (C x)) ≤
      (6*B) * relativeEnergy u v t := by
    have hb' := integral_mono_ae hIC.fun_neg hIE (by
      filter_upwards [ae_restrict_mem measurableSet_fundamentalCell] with x hx
      exact stretching_energy_bound x (w x) hB (hgrad x hx))
    simpa only [integral_neg, integral_const_mul, relativeEnergy, w, Pi.sub_apply] using hb'
  have hmul := mul_nonpos_of_nonneg_of_nonpos hν hl
  change (∫ x in fundamentalCell, euclidDot (w x)
    (timePartial v t x-timePartial u t x)) ≤ _
  simp_rw [he, euclidDot_sub, euclidDot_add, euclidDot_neg, euclidDot_smul]
  rw [integral_sub ((hIG.fun_neg.fun_add (hIL.const_mul ν)).fun_sub hIA) hIC,
    integral_sub (hIG.fun_neg.fun_add (hIL.const_mul ν)) hIA,
    integral_add hIG.fun_neg (hIL.const_mul ν), integral_neg, integral_const_mul, hg, ha]
  linarith

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.ClassicalSolution.relativeEnergy_derivative_bound := @_root_.OAI.Solenoidal.ClassicalSolution.relativeEnergy_derivative_bound
