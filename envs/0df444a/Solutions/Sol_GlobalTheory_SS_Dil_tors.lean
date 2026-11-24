-- Prove2me | solution 1 for GlobalTheory.SS.Dil.tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:43.758371+00:00
-- url     : https://prove2.me/submissions/b36feb22-f2b3-4230-bfde-abd733ac4595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_SS_Dil_exists_lift
import Theorems.Thm_GlobalTheory_SS_Dil_dd_add
import Theorems.Thm_GlobalTheory_SS_Dil_dd_mul
import Theorems.Thm_GlobalTheory_SS_Dil_dd_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R B B' S : Type} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra B S] [Algebra B' S] (φ : B →ₐ[R] B') (hφ : ∀ b, algebraMap B' S (φ b) = algebraMap B S b) (π : R) (ϖ : S)
    (hϖ : algebraMap B' S (algebraMap R B' π) = ϖ) (hreg : ϖ ∈ nonZeroDivisors S) (hinj : Function.Injective φ)
    (hden : ∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) {n : ℕ} (u : Fin n → S) (x : Fin n → B)
    (hu : ∑ i, u i • dd R B' S (φ (x i)) ∈ Submodule.torsion S (S ⊗[B'] KaehlerDifferential R B')) :
    ∑ i, u i • dd R B S (x i) ∈ Submodule.torsion S (S ⊗[B] KaehlerDifferential R B) := by
  let ι := LocalizedModule.mkLinearMap (nonZeroDivisors S) (S ⊗[B] KaehlerDifferential R B)
  have hbij : ∀ k : ℕ, Function.Bijective
      (fun w : LocalizedModule (nonZeroDivisors S) (S ⊗[B] KaehlerDifferential R B) => ϖ ^ k • w) := fun k =>
    (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units ι ⟨ϖ ^ k, pow_mem hreg k⟩)
  have hϖ' : algebraMap B S (algebraMap R B π) = ϖ := by rw [← hφ, φ.commutes, hϖ]
  have hpow : ∀ (k : ℕ) b, dd R B S (algebraMap R B π ^ k * b) = ϖ ^ k • dd R B S b := fun k b => by
    rw [dd_mul, ← map_pow, dd_algebraMap, smul_zero, add_zero, map_pow, map_pow, hϖ']
  choose N c hc using hden
  choose D hD using fun b' => (hbij (N b')).2 (ι (dd R B S (c b')))
  have hD' : ∀ (k : ℕ) b b', algebraMap R B' π ^ k * b' = φ b → ϖ ^ k • D b' = ι (dd R B S b) := by
    intro k b b' e
    apply (hbij (N b')).1
    have e1 : algebraMap R B π ^ N b' * b = algebraMap R B π ^ k * c b' := hinj (by
      rw [map_mul, map_mul, map_pow, map_pow, φ.commutes, ← e, ← hc]; ring)
    have := hD b'
    simp only at this ⊢
    rw [smul_comm, this, ← map_smul, ← map_smul, ← hpow, ← hpow, e1]
  have hval : ∀ b', algebraMap B S (c b') = ϖ ^ N b' * algebraMap B' S b' := fun b' => by
    rw [← hφ, ← hc, map_mul, map_pow, hϖ]
  obtain ⟨l, hl⟩ := exists_lift (R := R) (S := S) D
    (fun x y => by
      apply (hbij (N x + N y)).1
      simp only
      rw [hD' _ (algebraMap R B π ^ N y * c x + algebraMap R B π ^ N x * c y) _ (by
        simp only [map_add, map_mul, map_pow, φ.commutes, ← hc]; ring), dd_add, hpow, hpow, map_add, map_smul,
        map_smul, ← hD' _ _ _ (hc x), ← hD' _ _ _ (hc y), smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm (N y)])
    (fun x y => by
      apply (hbij (N x + N y)).1
      simp only
      rw [hD' _ (c x * c y) _ (by
        simp only [map_mul, ← hc]; ring), dd_mul, map_add, map_smul,
        map_smul, ← hD' _ _ _ (hc x), ← hD' _ _ _ (hc y), hval, hval, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 2 <;> ring)
    (fun r => by
      have := hD' 0 (algebraMap R B r) (algebraMap R B' r) (by simp)
      rwa [pow_zero, one_smul, dd_algebraMap, map_zero] at this)
  have hlφ : ∀ b, l (dd R B' S (φ b)) = ι (dd R B S b) := fun b => by
    have := hD' 0 b (φ b) (by simp)
    rw [pow_zero, one_smul] at this
    rw [← this]; exact hl _
  obtain ⟨r, hr⟩ := hu
  have h1 : ι ((r : S) • ∑ i, u i • dd R B S (x i)) = 0 := by
    have := congrArg l hr
    rw [Submonoid.smul_def, map_smul, map_sum, map_zero] at this
    simp only [map_smul, hlφ] at this
    rw [map_smul, map_sum]
    simpa only [map_smul] using this
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) ι).1 h1
  exact ⟨s * r, by rw [mul_smul]; exact hs⟩
end GlobalTheory.SS.Dil
