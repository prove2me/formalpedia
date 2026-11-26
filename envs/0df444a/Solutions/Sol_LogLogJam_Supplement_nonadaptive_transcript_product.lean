-- Prove2me | solution 1 for LogLogJam.Supplement.nonadaptive_transcript_product
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:21:10.914325+00:00
-- url     : https://prove2.me/submissions/c6df242d-7d9d-4c23-8b25-e69237a4b23e

import Definitions.Def_BosonicLearn_transcriptLaw
open MeasureTheory ProbabilityTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

private theorem nonadaptive_rec {N : ℕ} {O : Type} [MeasurableSpace O]
    (κ : (i : Fin N) → Kernel (Fin i → O) O) (ν : Fin N → Measure O)
    [∀ i, IsProbabilityMeasure (ν i)] (hκ : ∀ i x, κ i x = ν i) (t : ℕ) (ht : t ≤ N) :
    sequentialLaw κ t ht = Measure.pi (fun i : Fin t => ν (Fin.castLE ht i)) := by
  induction t with
  | zero => exact (Measure.pi_of_empty _ _).symm
  | succ t ih =>
    let ht' := Nat.le_of_succ_le ht
    let last : Fin N := ⟨t,ht⟩
    let u := fun i : Fin (t+1) => ν (Fin.castLE ht i)
    have hkernel : κ last = Kernel.const (Fin t → O) (ν last) := Kernel.ext fun a => by rw [hκ]; rfl
    unfold sequentialLaw
    rw [ih ht',hkernel,Measure.compProd_const]
    have h := (measurePreserving_piFinSuccAbove u (Fin.last t)).symm
    have s := (Measure.measurePreserving_swap (μ := Measure.pi fun i : Fin t => ν (Fin.castLE ht' i)) (ν := ν last))
    have hπ : (fun i : Fin t => u ((Fin.last t).succAbove i)) = fun i => ν (Fin.castLE ht' i) := by
      funext i; simp [u]
    rw [hπ] at h
    have e := h.comp s
    convert e.map_eq using 1
    congr 1
    funext x
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl

theorem solution {n N : ℕ} {O : Type} [MeasurableSpace O] [Inhabited O]
    (S : AdaptiveScheme n N O) (ρ : State (Occupation (Fin n)))
    (h : ∀ (i : Fin N) (x y : Fin i → O), S.povm i x = S.povm i y) :
    transcriptLaw S ρ.coefficients = Measure.pi (fun i => (S.povm i (fun _ => default)).law ρ.coefficients) := by
  let ν := fun i : Fin N => (S.povm i (fun _ => default)).law ρ.coefficients
  letI (i : Fin N) : IsProbabilityMeasure (ν i) := (S.povm i _).law_prob _ ρ.density
  apply nonadaptive_rec (S.round ρ.coefficients) ν
  intro i x
  rw [S.round_born _ ρ.density, h i x (fun _ => default)]
