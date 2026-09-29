-- Prove2me | solution 1 for ModularCurve.exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/849ab41d-1b35-53b7-a63a-8294cb31a1ae

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve IntermediateField

set_option hygiene false in
scoped notation "Qb" => AlgebraicClosure ℚ
set_option hygiene false in
scoped notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace RRDescent

theorem exists_finiteDimensional_forall_coeffMap_eq (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (x : LaurentSeries Qb) (hx : x ∈ laurentBaseChange Qb F₀) :
    ∃ E : IntermediateField ℚ Qb, FiniteDimensional ℚ E ∧
      ∀ σ : Gal, σ ∈ E.fixingSubgroup → coeffMap (σ : Qb →+* Qb) x = x := by
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, _, rfl⟩ := hx
    exact ⟨⊥, inferInstance, fun σ _ => coeffMap_coeffEmb σ y⟩
  | algebraMap c =>
    refine ⟨IntermediateField.adjoin ℚ {c}, IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic c).isIntegral,
      fun σ hσ => ?_⟩
    rw [coeffMap_algebraMap]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ c (IntermediateField.mem_adjoin_simple_self ℚ c)
  | add x y hx hy ihx ihy =>
    obtain ⟨E₁, h₁, hf₁⟩ := ihx
    obtain ⟨E₂, h₂, hf₂⟩ := ihy
    haveI := h₁; haveI := h₂
    refine ⟨E₁ ⊔ E₂, IntermediateField.finiteDimensional_sup E₁ E₂, fun σ hσ => ?_⟩
    rw [map_add, hf₁ σ ?_, hf₂ σ ?_]
    · rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢; exact fun z hz => hσ z ((le_sup_right : E₂ ≤ E₁ ⊔ E₂) hz)
    · rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢; exact fun z hz => hσ z ((le_sup_left : E₁ ≤ E₁ ⊔ E₂) hz)
  | mul x y hx hy ihx ihy =>
    obtain ⟨E₁, h₁, hf₁⟩ := ihx
    obtain ⟨E₂, h₂, hf₂⟩ := ihy
    haveI := h₁; haveI := h₂
    refine ⟨E₁ ⊔ E₂, IntermediateField.finiteDimensional_sup E₁ E₂, fun σ hσ => ?_⟩
    rw [map_mul, hf₁ σ ?_, hf₂ σ ?_]
    · rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢; exact fun z hz => hσ z ((le_sup_right : E₂ ≤ E₁ ⊔ E₂) hz)
    · rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢; exact fun z hz => hσ z ((le_sup_left : E₁ ≤ E₁ ⊔ E₂) hz)
  | inv x hx ihx =>
    obtain ⟨E₁, h₁, hf₁⟩ := ihx
    exact ⟨E₁, h₁, fun σ hσ => by rw [map_inv₀, hf₁ σ hσ]⟩

end RRDescent

open RRDescent

set_option maxHeartbeats 6400000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hE : ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • E = E)
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(xHFunctionFieldBar M H),
      (∀ i, b i ∈ riemannRochSpace E) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • b i = b i := by
  classical

  let act : Gal →* SemilinearAut Qb ↥(xHFunctionFieldBar M H) := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H)
  let V : Submodule Qb ↥(xHFunctionFieldBar M H) := riemannRochSpace E

  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : Normal ℚ Qb := ⟨fun x => IsAlgClosed.splits _⟩
  haveI : Algebra.IsSeparable ℚ Qb := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ Qb := IsGalois.mk

  have hopenF : ∀ f : ↥(xHFunctionFieldBar M H), ∃ Ef : IntermediateField ℚ Qb, FiniteDimensional ℚ Ef ∧
      ∀ σ : Gal, σ ∈ Ef.fixingSubgroup → act σ • f = f := by
    intro f
    obtain ⟨Ef, hfd, hfix⟩ := exists_finiteDimensional_forall_coeffMap_eq (xHFunctionField M H) f.1 f.2
    exact ⟨Ef, hfd, fun σ hσ => Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact hfix σ hσ)⟩

  have hact_smul : ∀ (σ : Gal) (c : Qb) (f : ↥(xHFunctionFieldBar M H)), act σ • (c • f) = σ c • (act σ • f) := by
    intro σ c f
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', SemilinearAut.smul_algebraMap]
    rfl

  have hstabE : ∀ (σ : Gal), act σ • E = E → ∀ f ∈ V, act σ • f ∈ V := by
    intro σ hσ f hf
    rw [mem_riemannRochSpace_iff] at hf ⊢
    intro W
    rcases hf ((act σ)⁻¹ • W) with h | h
    · left; rw [h, smul_zero]
    · right
      have h1 : ((act σ) • ((act σ)⁻¹ • W)).ord ((act σ) • f) = ((act σ)⁻¹ • W).ord f :=
        SemilinearAut.ord_smul (act σ) ((act σ)⁻¹ • W) f
      rw [smul_inv_smul] at h1
      rw [h1]
      have h2 : E ((act σ)⁻¹ • W) = E W := by
        conv_rhs => rw [← hσ]
        rw [SemilinearAut.divisor_smul_apply]
      rw [h2] at h
      exact h
  have hstabE_inv : ∀ (σ : Gal), act σ • E = E → act σ⁻¹ • E = E := by
    intro σ hσ
    rw [map_inv]
    exact inv_smul_eq_iff.mpr hσ.symm

  let Hst : Subgroup Gal :=
    { carrier := {σ | ∀ f ∈ V, act σ • f ∈ V ∧ act σ⁻¹ • f ∈ V}
      one_mem' := fun f hf => by simp [hf]
      mul_mem' := fun {σ τ} hσ hτ f hf => by
        constructor
        · rw [map_mul, mul_smul]; exact (hσ _ (hτ f hf).1).1
        · rw [mul_inv_rev, map_mul, mul_smul]; exact (hτ _ (hσ f hf).2).2
      inv_mem' := fun {σ} hσ f hf => ⟨(hσ f hf).2, by rw [inv_inv]; exact (hσ f hf).1⟩ }
  have hHmem : ∀ {σ : Gal}, σ ∈ Hst ↔ ∀ f ∈ V, act σ • f ∈ V ∧ act σ⁻¹ • f ∈ V := Iff.rfl
  have hSH : ∀ σ ∈ S, σ ∈ Hst := fun σ hσ =>
    hHmem.mpr fun f hf => ⟨hstabE σ (hE σ hσ) f hf, hstabE σ⁻¹ (hstabE_inv σ (hE σ hσ)) f hf⟩

  let fam := Module.finBasis Qb V
  choose Ef hEfd hEfix using fun i : Fin (Module.finrank Qb V) => hopenF (fam i : ↥(xHFunctionFieldBar M H))
  haveI : ∀ i, FiniteDimensional ℚ (Ef i) := hEfd
  let Etot : IntermediateField ℚ Qb := ⨆ i, Ef i
  haveI : FiniteDimensional ℚ Etot := IntermediateField.finiteDimensional_iSup_of_finite
  have hUfix : ∀ (σ : Gal), σ ∈ Etot.fixingSubgroup → ∀ i, act σ • (fam i : ↥(xHFunctionFieldBar M H)) = fam i := by
    intro σ hσ i
    apply hEfix i σ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun x hx => hσ x ((le_iSup Ef i) hx)
  have hUstab : ∀ (σ : Gal), σ ∈ Etot.fixingSubgroup → ∀ f ∈ V, act σ • f ∈ V := by
    intro σ hσ f hf
    have hrepr := fam.sum_repr ⟨f, hf⟩
    have hf' : f = ∑ i, (fam.repr ⟨f, hf⟩ i) • (fam i : ↥(xHFunctionFieldBar M H)) := by
      have := congrArg (Submodule.subtype V) hrepr
      simp only [map_sum, map_smul, Submodule.subtype_apply] at this
      exact this.symm
    rw [hf', Finset.smul_sum]
    refine V.sum_mem fun i _ => ?_
    rw [hact_smul, hUfix σ hσ i]
    exact V.smul_mem _ (fam i).2
  have hUH : Etot.fixingSubgroup ≤ Hst := fun σ hσ =>
    hHmem.mpr fun f hf => ⟨hUstab σ hσ f hf, hUstab σ⁻¹ (Subgroup.inv_mem _ hσ) f hf⟩
  have hHopen : IsOpen (Hst : Set Gal) :=
    Subgroup.isOpen_mono hUH (IntermediateField.fixingSubgroup_isOpen Etot)
  have hHclosed : IsClosed (Hst : Set Gal) := Subgroup.isClosed_of_isOpen Hst hHopen
  let Hc : ClosedSubgroup Gal := ⟨Hst, hHclosed⟩
  let K₀ : IntermediateField ℚ Qb := IntermediateField.fixedField Hst
  have hfixK₀ : K₀.fixingSubgroup = Hst := InfiniteGalois.fixingSubgroup_fixedField Hc

  haveI : IsGalois K₀ Qb := IsGalois.tower_top_of_isGalois ℚ K₀ Qb
  have hres : ∀ σ' : Qb ≃ₐ[K₀] Qb, σ'.restrictScalars ℚ ∈ Hst := by
    intro σ'
    rw [← hfixK₀, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ'.commutes ⟨x, hx⟩
  let ρ : (Qb ≃ₐ[K₀] Qb) → V →+ V := fun σ' =>
    { toFun := fun f => ⟨act (σ'.restrictScalars ℚ) • (f : ↥(xHFunctionFieldBar M H)), ((hres σ') f f.2).1⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun a b => Subtype.ext (smul_add _ _ _) }
  have hρ_apply : ∀ (σ' : Qb ≃ₐ[K₀] Qb) (f : V), ((ρ σ' f : V) : ↥(xHFunctionFieldBar M H)) = act (σ'.restrictScalars ℚ) • (f : ↥(xHFunctionFieldBar M H)) :=
    fun _ _ => rfl
  have hρ_smul : ∀ (σ' : Qb ≃ₐ[K₀] Qb) (a : Qb) (v : V), ρ σ' (a • v) = σ' a • ρ σ' v := by
    intro σ' a v
    apply Subtype.ext
    rw [hρ_apply, Submodule.coe_smul, Submodule.coe_smul, hρ_apply, hact_smul]
    rfl
  have hρ_one : ∀ v : V, ρ 1 v = v := by
    intro v
    apply Subtype.ext
    rw [hρ_apply]
    have : (1 : Qb ≃ₐ[K₀] Qb).restrictScalars ℚ = 1 := rfl
    rw [this, map_one, one_smul]
  have hρ_mul : ∀ (σ' τ' : Qb ≃ₐ[K₀] Qb) (v : V), ρ (σ' * τ') v = ρ σ' (ρ τ' v) := by
    intro σ' τ' v
    apply Subtype.ext
    rw [hρ_apply, hρ_apply, hρ_apply]
    have : (σ' * τ').restrictScalars ℚ = σ'.restrictScalars ℚ * τ'.restrictScalars ℚ := rfl
    rw [this, map_mul, mul_smul]
  have hopen' : ∀ v : V, ∃ E' : IntermediateField K₀ Qb, FiniteDimensional K₀ E' ∧
      ∀ σ' : Qb ≃ₐ[K₀] Qb, σ' ∈ E'.fixingSubgroup → ρ σ' v = v := by
    intro v
    obtain ⟨Ev, hvfd, hvfix⟩ := hopenF (v : ↥(xHFunctionFieldBar M H))
    haveI := hvfd
    let bv := Module.finBasis ℚ Ev
    haveI : Algebra.IsAlgebraic K₀ Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) K₀
    refine ⟨IntermediateField.adjoin K₀ (Set.range fun i => ((bv i : Ev) : Qb)),
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x), fun σ' hσ' => ?_⟩
    apply Subtype.ext
    rw [hρ_apply]
    apply hvfix
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ' ⊢
    intro x hx

    have hx' : (⟨x, hx⟩ : Ev) = ∑ i, (bv.repr ⟨x, hx⟩ i) • bv i := (bv.sum_repr ⟨x, hx⟩).symm
    have hxQ : x = ∑ i, (bv.repr ⟨x, hx⟩ i) • ((bv i : Ev) : Qb) := by
      have h1 : (((⟨x, hx⟩ : Ev)) : Qb) = ((∑ i, (bv.repr ⟨x, hx⟩ i) • bv i : Ev) : Qb) :=
        congrArg (fun z : Ev => (z : Qb)) hx'
      rw [AddSubmonoidClass.coe_finsetSum] at h1
      exact h1
    rw [hxQ]
    show σ' (∑ i, (bv.repr ⟨x, hx⟩ i) • ((bv i : Ev) : Qb)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_rat_smul]
    congr 1
    exact hσ' _ (IntermediateField.subset_adjoin K₀ _ ⟨i, rfl⟩)
  obtain ⟨b, hb⟩ := Module.exists_basis_forall_semilinear_apply_eq_of_isGalois K₀ Qb V ρ hρ_smul hρ_one hρ_mul hopen'

  refine ⟨fun i => (b i : ↥(xHFunctionFieldBar M H)), fun i => (b i).2, ?_, ?_⟩
  · exact b.linearIndependent.map' V.subtype V.ker_subtype
  · intro i σ hσ
    have hσH : σ ∈ Hst := hSH σ hσ
    have hσK₀ : ∀ x ∈ K₀, σ x = x := fun x hx => hx ⟨σ, hσH⟩
    let σ' : Qb ≃ₐ[K₀] Qb := { σ with commutes' := fun x => hσK₀ x x.2 }
    have h1 : σ'.restrictScalars ℚ = σ := rfl
    have h2 := congrArg (fun v : V => (v : ↥(xHFunctionFieldBar M H))) (hb i σ')
    simp only [hρ_apply, h1] at h2
    exact h2

end S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH
end P2MW
export P2MW.S_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH (solution)
