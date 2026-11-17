-- Prove2me | solution 1 for N25.GlobalKummer.cyclotomic_cocycle_kummer
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:45.782004+00:00
-- url     : https://prove2.me/submissions/a372b2b5-227d-44b8-a528-2fb736f344ca

import Theorems.Thm_N25_GlobalKummer_cyclotomic_roots_equiv
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance instL_N25_GlobalKummer_cyclotomic_cocycle_kumm_23397f_se26115 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- A continuous cocycle on the literal cyclotomic line has rational Kummer
data after an equivariant identification with actual roots of unity. -/
theorem _root_.solution
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (hc : groupCohomology.IsLevelConstant₁ (MonoidHom.id Gal) c) :
    ∃ (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
      (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ),
      (∀ (σ : Gal) (b : ZMod 71),
        e ((ExtCitation.cycloChar 71 σ : ZMod 71) * b) =
          Additive.ofMul (σ • Additive.toMul (e b))) ∧
      algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ) = (α : AlgebraicClosure ℚ) ^ 71 ∧
      ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
        groupCohomology.Kummer.kummerCocycle α σ := by
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    { isAlgClosed := AlgebraicClosure.isAlgClosed ℚ
      isAlgebraic := ⟨fun z => by
        have hz : IsIntegral ℚ z := by
          convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
          all_goals rfl
        exact hz.isAlgebraic⟩ }
  letI : IsGalois ℚ (AlgebraicClosure ℚ) :=
    { to_isSeparable := IsAlgClosure.separable ℚ (AlgebraicClosure ℚ)
      to_normal := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) }
  obtain ⟨e, he⟩ := cyclotomic_roots_equiv
  let f : Gal → (AlgebraicClosure ℚ)ˣ := fun σ => (Additive.toMul (e (c σ))).val
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    have hcc : c (σ * τ) = (ExtCitation.cycloChar 71 σ : ZMod 71) * c τ + c σ :=
      (groupCohomology.mem_cocycles₁_iff _).mp c.property σ τ
    change (Additive.toMul (e (c (σ * τ)))).val =
      σ • (Additive.toMul (e (c τ))).val * (Additive.toMul (e (c σ))).val
    rw [hcc, map_add, he]
    rfl
  have hfp : ∀ σ : Gal, f σ ^ 71 = 1 := by
    intro σ
    simpa only [mem_rootsOfUnity] using (Additive.toMul (e (c σ))).property
  have hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ τ : Gal, τ ∈ F.fixingSubgroup → f (σ * τ) = f σ := by
    obtain ⟨F, hF, hfix⟩ := hc
    exact ⟨F, hF, fun σ τ hτ => congrArg
      (fun b : cyclotomicRep => (Additive.toMul (e b)).val) (hfix σ τ hτ)⟩
  obtain ⟨a, α, hα, hfα⟩ :=
    groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_of_level
      (p := 71) hf hfp hlc
  exact ⟨e, a, α, he, hα, hfα⟩

end N25.GlobalKummer
