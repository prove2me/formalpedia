-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.fin_append_linear_isometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:36:54.025339+00:00
-- url     : https://prove2.me/submissions/1c043d59-ef2b-4a49-bce1-1e660fd0d8b3

import Definitions.Def_OAI_PiExponent_DeterminantContradiction_UnitBoxes
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Isometry

section

open MeasureTheory Set

namespace PiL3

theorem lin_ext {α V : Type*} [Fintype α] [AddCommGroup V] [Module Complex V]
    [FiniteDimensional Complex V]
    (v : α → V) (h : LinearIndependent Complex v) (values : α → Complex) :
    ∃ L : V →ₗ[Complex] Complex, ∀ i, L (v i) = values i := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.linearCombination Complex values) ∘ₗ h.repr)
  refine ⟨g, fun i => ?_⟩
  have := congrArg (fun F => F ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
  rw [this, h.repr_eq_single i _ rfl, Finsupp.linearCombination_single, one_smul]

theorem indep_cols {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {K : Type*} [Field K] (A : Matrix α β K)
    (h : Function.Surjective A.mulVecLin) :
    ∃ selection : α → β,
      Function.Injective selection ∧
        LinearIndependent K (fun j : α => fun i : α => A i (selection j)) := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  have htop : Submodule.span K (Set.range (A.col ∘ a)) = ⊤ := by
    rw [hsp, ← Matrix.range_mulVecLin, LinearMap.range_eq_top.2 h]
  have : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  let b := Module.Basis.mk hli htop.ge
  have hc : Fintype.card κ = Fintype.card α := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  obtain ⟨e⟩ := Fintype.card_eq.1 hc.symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  exact hli.comp e e.injective

theorem fin_append (m : Nat) :
    ∃ e : ((Fin m → Real) × (Fin 1 → Real)) ≃ₗᵢ[Real] (Fin (m + 1) → Real),
      ∀ f g, e (f, g) = Fin.append f g := by
  let L : ((Fin m → Real) × (Fin 1 → Real)) ≃ₗ[Real] (Fin (m + 1) → Real) :=
    { Fin.appendEquiv m 1 with
      map_add' := fun x y => by
        ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.appendEquiv]
      map_smul' := fun c x => by
        ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.appendEquiv] }
  refine ⟨{ L with norm_map' := fun x => ?_ }, fun f g => rfl⟩
  have := (Fin.appendIsometry (α := ℝ) m 1).isometry.norm_map_of_map_zero (by ext i; show Fin.append (0 : Fin m → ℝ) 0 i = 0; induction i using Fin.addCases <;> simp)
  exact this x

theorem coord_split (m : Nat) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) :
    MeasureTheory.volume ((fun p : (Fin m → Real) × Real => fun i : Fin (m + 1) => Fin.lastCases p.2 p.1 i) ⁻¹' s) =
      MeasureTheory.volume s := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have hsw : MeasurePreserving (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ)) volume volume :=
    Measure.measurePreserving_swap
  have hf := h.comp hsw
  have hfun : (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘ Prod.swap) =
      (fun p : (Fin m → Real) × Real => fun i : Fin (m + 1) => Fin.lastCases p.2 p.1 i) := by
    funext p i
    induction i using Fin.lastCases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rw [hfun] at hf
  exact hf.measure_preimage hs.nullMeasurableSet

theorem encoded (m : Nat) (P : MvPolynomial (Fin m) Complex)
    (a : Fin m → Nat)
    (h : a ∉ P.support.map Finsupp.equivFunOnFinite.toEmbedding) :
    P.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector a) = 0 := by
  by_contra hne
  apply h
  rw [Finset.mem_map]
  refine ⟨_, MvPolynomial.mem_support_iff.2 hne, ?_⟩
  simp [OAI.PiExponent.InterpolationMatrix.exponentVector]

lemma unitBox_eq {n : ℕ} (a : Fin n → ℕ) :
    OAI.PiExponent.DeterminantContradiction.unitBox a =
      Set.pi univ fun i => Ico (a i : ℝ) (a i + 1) := by
  ext x; simp [OAI.PiExponent.DeterminantContradiction.unitBox]

lemma vol_unitBox {n : ℕ} (a : Fin n → ℕ) :
    volume (OAI.PiExponent.DeterminantContradiction.unitBox a) = 1 := by
  rw [unitBox_eq, Real.volume_pi_Ico]; simp

theorem box_lower {n : ℕ} (S : Finset (Fin n → ℕ)) :
    ENNReal.ofReal (S.card : ℝ) ≤ MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.unitBoxUnion S) := by
  rw [OAI.PiExponent.DeterminantContradiction.unitBoxUnion, Finset.set_biUnion_coe, measure_biUnion_finset]
  · simp [vol_unitBox]
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    apply hab
    funext i
    obtain ⟨h1, h2⟩ := hxa i
    obtain ⟨h3, h4⟩ := hxb i
    have e1 : (a i : ℝ) < b i + 1 := lt_of_le_of_lt h1 h4
    have e2 : (b i : ℝ) < a i + 1 := lt_of_le_of_lt h3 h2
    have e1' : a i < b i + 1 := by exact_mod_cast e1
    have e2' : b i < a i + 1 := by exact_mod_cast e2
    omega
  · intro a _
    rw [unitBox_eq]
    exact MeasurableSet.univ_pi fun i => measurableSet_Ico

theorem box_upper {m : Nat} (S : Finset (Fin m → Nat)) :
    (MeasureTheory.volume (⋃ n ∈ S,
      {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1})).toReal ≤ (S.card : Real) := by
  have : volume (⋃ n ∈ S, {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1}) ≤ S.card := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have := fun n : Fin m → ℕ => vol_unitBox n
    simp only [OAI.PiExponent.DeterminantContradiction.unitBox] at this
    simp [this]
  have h2 := ENNReal.toReal_mono (by simp) this
  simpa using h2

end PiL3

end

open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) :
    ∃ e : ((Fin m → Real) × (Fin 1 → Real)) ≃ₗᵢ[Real] (Fin (m + 1) → Real),
      ∀ f g, e (f, g) = Fin.append f g := by
  apply PiL3.fin_append <;> assumption
