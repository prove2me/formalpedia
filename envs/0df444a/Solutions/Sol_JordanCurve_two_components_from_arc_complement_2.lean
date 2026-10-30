-- Prove2me | solution 2 for JordanCurve.two_components_from_arc_complement
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T01:44:51.320376+00:00
-- url     : https://prove2.me/submissions/0ca8d89c-9e41-481f-b92f-6bf35f6e3488

/-
Reconstructed from the accepted Prove2me proofs by Mazecto for
JordanCurve.euclidean_unit_circle_loop, circle_embedding_is_schoenflies_jordan,
and jordan_curve_theorem, using the Schoenflies development by Álvaro Begué.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Schoenflies_Jordan
import Definitions.Def_Schoenflies_SquareCycle


open Set Metric

noncomputable section

theorem localUnitCircleLoop :
    ∃ e : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ContinuousOn e (Set.Icc 0 1) ∧ e 0 = e 1 ∧
      Set.InjOn e (Set.Ico 0 1) ∧ e '' Set.Icc 0 1 = Set.univ := by
  let L : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr
  let F : Circle → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun z => ⟨L (z : ℂ), by
      apply mem_sphere_zero_iff_norm.mpr
      simpa using z.norm_coe⟩
  have hFinj : Function.Injective F := by
    intro z w h
    apply Subtype.ext
    exact L.injective (congrArg Subtype.val h)
  have hFsurj : Function.Surjective F := by
    intro w
    let z : ℂ := L.symm w.1
    have hw : L z = w.1 := L.apply_symm_apply _
    have hz : z ∈ Submonoid.unitSphere ℂ := by
      change z ∈ Metric.sphere (0 : ℂ) 1
      apply mem_sphere_zero_iff_norm.mpr
      have hn : ‖L z‖ = 1 := mem_sphere_zero_iff_norm.mp (hw.symm ▸ w.2)
      simpa using hn
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hw
  have hFcont : Continuous F :=
    Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _
  let e : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun t => F (Circle.exp (2 * Real.pi * t - Real.pi))
  have hecont : Continuous e := by
    exact hFcont.comp (Circle.exp.continuous.comp (by fun_prop))
  have heclose : e 0 = e 1 := by
    have harg : Circle.exp (2 * Real.pi * (0 : ℝ) - Real.pi) =
        Circle.exp (2 * Real.pi * (1 : ℝ) - Real.pi) := by
      convert (Circle.exp_add_two_pi (-Real.pi)).symm using 1 <;> ring
    exact congrArg F harg
  have heinj : Set.InjOn e (Set.Ico 0 1) := by
    intro s hs t ht h
    have heq : Circle.exp (2 * Real.pi * s - Real.pi) =
        Circle.exp (2 * Real.pi * t - Real.pi) := hFinj h
    have hs' : 2 * Real.pi * s - Real.pi ∈ Set.Ico (-Real.pi) Real.pi := by
      constructor
      · nlinarith [hs.1, Real.pi_pos]
      · have hp : 0 < 2 * Real.pi := by positivity
        nlinarith [mul_lt_mul_of_pos_left hs.2 hp]
    have ht' : 2 * Real.pi * t - Real.pi ∈ Set.Ico (-Real.pi) Real.pi := by
      constructor
      · nlinarith [ht.1, Real.pi_pos]
      · have hp : 0 < 2 * Real.pi := by positivity
        nlinarith [mul_lt_mul_of_pos_left ht.2 hp]
    have hst := Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi)
      (by nlinarith) hs' ht' heq
    nlinarith [hst, Real.pi_pos]
  have heimage : e '' Set.Icc 0 1 = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro w
    obtain ⟨z, rfl⟩ := hFsurj w
    obtain ⟨x, hx, hzx⟩ := Circle.surjOn_exp_neg_pi_pi (Set.mem_univ z)
    let t : ℝ := (x + Real.pi) / (2 * Real.pi)
    have hp : 0 < 2 * Real.pi := by positivity
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [hx.1]) hp.le
      · apply (div_le_iff₀ hp).2
        linarith [hx.2]
    have hangle : 2 * Real.pi * t - Real.pi = x := by
      dsimp [t]
      field_simp
      ring
    refine ⟨t, ht, ?_⟩
    change F (Circle.exp (2 * Real.pi * t - Real.pi)) = F z
    rw [hangle]
    exact congrArg F hzx
  exact ⟨e, hecont.continuousOn, heclose, heinj, heimage⟩


theorem localCircleIsJordan
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    Schoenflies.IsJordanCurve (Set.range γ) := by
  obtain ⟨e, hec, heclose, heinj, herange⟩ :=
    localUnitCircleLoop
  refine ⟨fun t => γ (e t), ⟨hγ.comp_continuousOn hec,
    congrArg γ heclose, ?_⟩, ?_⟩
  · intro s hs t ht hst
    exact heinj hs ht (hinj hst)
  · change (fun t => γ (e t)) '' Set.Icc (0 : ℝ) 1 = Set.range γ
    rw [← Set.image_image, herange, Set.image_univ]


theorem solution
    (_hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α → IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ a b : EuclideanSpace ℝ (Fin 2),
      a ∉ Set.range γ ∧ b ∉ Set.range γ ∧
      Disjoint (connectedComponentIn ((Set.range γ)ᶜ) a)
        (connectedComponentIn ((Set.range γ)ᶜ) b) ∧
      connectedComponentIn ((Set.range γ)ᶜ) a ∪
        connectedComponentIn ((Set.range γ)ᶜ) b = (Set.range γ)ᶜ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) b) := by
  let C : Set (EuclideanSpace ℝ (Fin 2)) := Set.range γ
  have hcurve : Schoenflies.IsJordanCurve C := localCircleIsJordan γ hγ hinj
  have hsep : Schoenflies.IsSeparating C :=
    Schoenflies.IsJordanCurve.isSeparating
      (fun A hA => Schoenflies.isConnected_compl_arc hA Schoenflies.squaresTwoConnected)
      hcurve
  obtain ⟨a, ha⟩ := hsep.isConnected_inside.nonempty
  obtain ⟨b, hb⟩ := hsep.isConnected_outside.nonempty
  have hca : connectedComponentIn Cᶜ a = Schoenflies.inside C :=
    hsep.connectedComponentIn_eq_inside ha
  have hcb : connectedComponentIn Cᶜ b = Schoenflies.outside C :=
    hsep.connectedComponentIn_eq_outside hb
  refine ⟨a, b, Schoenflies.inside_subset_compl ha, Schoenflies.outside_subset_compl hb,
    ?_, ?_, ?_, ?_⟩
  · rw [hca, hcb]
    exact Set.disjoint_left.mpr (fun _ hi ho => ho.2 hi.2)
  · rw [hca, hcb]
    exact Schoenflies.inside_union_outside C
  · rw [hca]
    exact hsep.isBounded_inside
  · rw [hcb]
    exact hsep.not_isBounded_outside

