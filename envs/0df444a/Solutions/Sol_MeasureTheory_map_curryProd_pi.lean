-- Prove2me | solution 1 for MeasureTheory.map_curryProd_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:04.099876+00:00
-- url     : https://prove2.me/submissions/15d67401-4977-4c9e-a699-08162f5b4e37

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory
variable {ιp κp : Type*} [Fintype ιp] [Fintype κp] {α : ιp × κp → Type*}
  [∀ p, MeasurableSpace (α p)] (ν : (p : ιp × κp) → Measure (α p)) [∀ p, SigmaFinite (ν p)]
namespace MeasureTheory
theorem _root_.solution :
    Measure.map (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) (Measure.pi ν)
      = Measure.pi (fun i => Measure.pi (fun j => ν (i, j))) := by
  have hmeas : Measurable (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) := by
    apply measurable_pi_iff.mpr; intro i; apply measurable_pi_iff.mpr; intro j
    exact measurable_pi_apply (i, j)
  refine (Measure.pi_eq_generateFrom
      (μ := fun i => Measure.pi (fun j => ν (i, j)))
      (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
      (fun i => Measure.FiniteSpanningSetsIn.pi (fun j => (ν (i, j)).toFiniteSpanningSetsIn))
      ?_).symm
  intro s hs
  have hbox : ∀ i, ∃ t : (j : κp) → Set (α (i, j)),
      (∀ j, MeasurableSet (t j)) ∧ Set.pi univ t = s i := by
    intro i
    obtain ⟨a, ha, hae⟩ := hs i
    exact ⟨a, fun j => ha j (mem_univ j), hae⟩
  choose t ht hts using hbox
  have hsmeas : ∀ i, MeasurableSet (s i) := by
    intro i; rw [← hts i]; exact MeasurableSet.univ_pi (ht i)
  have hpre : (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) ⁻¹' (Set.pi univ s)
      = Set.pi univ (fun p : ιp × κp => t p.1 p.2) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h p
      have h1 := h p.1
      rw [← hts p.1, Set.mem_pi] at h1
      exact h1 p.2 (mem_univ _)
    · intro h i
      rw [← hts i, Set.mem_pi]
      exact fun j _ => h (i, j)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hsmeas), hpre, Measure.pi_pi]
  have hrhs : ∏ i, (Measure.pi (fun j => ν (i, j))) (s i)
      = ∏ i, ∏ j, ν (i, j) (t i j) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← hts i, Measure.pi_pi]
  rw [hrhs, Fintype.prod_prod_type (f := fun p : ιp × κp => ν p (t p.1 p.2))]
end MeasureTheory
