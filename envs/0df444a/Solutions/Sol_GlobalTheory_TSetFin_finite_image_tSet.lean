-- Prove2me | solution 1 for GlobalTheory.TSetFin.finite_image_tSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:22.151152+00:00
-- url     : https://prove2.me/submissions/58896caf-7ccf-495f-b117-244796422e2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Theorems.Thm_GlobalTheory_TSetFin_local_int
import Theorems.Thm_GlobalTheory_TSetFin_triv_mul
import Theorems.Thm_GlobalTheory_TSetFin_triv_inv
import Theorems.Thm_GlobalTheory_TSetFin_mem_Umax_of_loc
import Theorems.Thm_GlobalTheory_TSetFin_glint_int
import Theorems.Thm_GlobalTheory_TSetFin_approx_class

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
open GlobalTheory GlobalTheory.TSetFin
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace GlobalTheory.TSetFin
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
    s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ →
    ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  intro L _ _ _ n J χ B hJ s ϖ k hB hϖ
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : Formalism.AUTREP.GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ Formalism.AUTREP.tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ Formalism.AUTREP.tSet L n s ϖ k, ∀ x' ∈ Formalism.AUTREP.tSet L n s ϖ k, κ x = κ x' →
      (x : Formalism.AUTREP.GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine ((hJ _ ?_).1).2 ?_
    · intro w hw
      refine htriv w ?_
      rintro rfl
      exact hB (by simpa using hw)
    · refine mem_Umax_of_loc s _ htriv (fun i j => ?_) (fun i j => ?_)
      · rw [map_mul, map_inv]; exact h1 i j
      · rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j
  let g : Formalism.AUTREP.GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ Formalism.AUTREP.tSet L n s ϖ k, (x : Formalism.AUTREP.GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : Formalism.AUTREP.GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg
end GlobalTheory.TSetFin
