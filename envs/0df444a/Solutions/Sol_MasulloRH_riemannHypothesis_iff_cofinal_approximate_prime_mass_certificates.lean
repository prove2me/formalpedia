-- Prove2me | solution 1 for MasulloRH.riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:58:17.341286+00:00
-- url     : https://prove2.me/submissions/dd62ccce-6e83-46f3-a787-93a9d62d5e7e

-- Dependency audit: the proposition on the right is the open mission certificate statement.
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_MasulloRH_cofinal_prime_slack_iff_off_line_mass_le
import Theorems.Thm_MasulloRH_cofinal_prime_slack_verifies_height_via_quartets
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open ArithmeticFunction MasulloRH Finset

theorem solution :
    let P := fun N : ℕ => Real.log 2/2 + Real.pi/4 - 37/30 +
      ∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))
    let M := fun F : Finset (ZetaZerosInTraceStrip (1/2)) =>
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
    RiemannHypothesis ↔
    (∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), (∀ z ∈ F, z.val.re = 1/2) ∧ P N ≤ M F + 1/((k:ℝ)+1)) := by
  classical
  let P := fun N : ℕ => Real.log 2/2 + Real.pi/4 - 37/30 +
    ∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))
  let Z := ZetaZerosInTraceStrip (1/2)
  let q (z : Z) := z.val.re = 1/2
  let L := {z : Z // q z}
  let w (z : Z) := (analyticOrderNatAt riemannZeta z.val:ℝ) *
    ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
  let C := ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset L, P N ≤ (∑ z ∈ F,w z.val)+ 0 + 1/((k:ℝ)+1)
  change RiemannHypothesis ↔ ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset Z, (∀ z ∈ F,q z) ∧ P N ≤ (∑ z ∈ F,w z)+1/((k:ℝ)+1)
  constructor
  · intro rh
    have hall (z : Z) : q z := riemannHypothesis_iff_zeros_in_strip_on_line.mp rh _ z.prop.1 z.prop.2.1 z.prop.2.2.1
    haveI : IsEmpty {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2} := ⟨fun z => z.prop (hall z.val)⟩
    have hc : C := (cofinal_prime_slack_iff_off_line_mass_le 0).mp (by simp)
    intro k
    obtain ⟨N,hN,F,hF⟩ := hc k
    refine ⟨N,hN,F.map (Function.Embedding.subtype q),fun z _ => hall z,?_⟩
    simpa only [Finset.sum_map,Function.Embedding.coe_subtype,add_zero,Function.comp_apply] using hF
  · intro h
    have hc : C := by
      intro k
      obtain ⟨N,hN,F,hline,hF⟩ := h k
      let e : {z // z ∈ F} ↪ L := ⟨fun z => ⟨z.val,hline z.val z.prop⟩,
        fun _ _ he => Subtype.ext (congrArg (fun u : L => u.val) he)⟩
      refine ⟨N,hN,F.attach.map e,?_⟩
      rw [Finset.sum_map,add_zero]
      change P N ≤ (∑ z ∈ F.attach,w z.val)+1/((k:ℝ)+1)
      simpa only [Finset.sum_attach] using hF
    apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
    intro s hs h0 h1
    let z : Z := ⟨s,hs,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    exact cofinal_prime_slack_verifies_height_via_quartets 0 hc |s.im| (by norm_num) z le_rfl
