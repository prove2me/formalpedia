-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a00b0ff7-cc5b-5e60-bf7d-b4cb80636b1b

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm

set_option autoImplicit false

noncomputable section

namespace W0A

open ModularCurve IntermediateField

local notation "Qb" => AlgebraicClosure ℚ

section Coeff

variable {R S : Type*} [Field R] [Field S]

theorem coeffMap_injective (f : R →+* S) : Function.Injective (coeffMap f) := fun x y h => by
  ext k
  have := congrArg (fun z => HahnSeries.coeff z k) h
  simpa [coeffMap_coeff] using f.injective this

theorem coeffMap_smul (f : R →+* S) (c : R) (x : LaurentSeries R) :
    coeffMap f (c • x) = f c • coeffMap f x := by
  ext k
  simp [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul]

theorem coeffMap_algebraMap' (f : R →+* S) (c : R) :
    coeffMap f (algebraMap R (LaurentSeries R) c) = algebraMap S (LaurentSeries S) (f c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

variable [CharZero R] [CharZero S]

theorem coeffMap_coeffEmb' (f : R →+* S) (y : LaurentSeries ℚ) :
    coeffMap f (coeffEmb R y) = coeffEmb S y := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) y

end Coeff

section Emb

variable (F : IntermediateField ℚ (LaurentSeries ℚ)) {L : Type} [Field L] [CharZero L]
  (ιA : L →+* Qb)

theorem coeffMap_mem_laurentBaseChange' {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F) :
    coeffMap ιA x ∈ laurentBaseChange Qb F := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange Qb F).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange Qb hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

def emb : ↥(laurentBaseChange L F) →+* ↥(laurentBaseChange Qb F) where
  toFun f := ⟨coeffMap ιA (f : LaurentSeries L), coeffMap_mem_laurentBaseChange' F ιA f.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[scoped simp] theorem coe_emb (f : ↥(laurentBaseChange L F)) :
    ((emb F ιA f : ↥(laurentBaseChange Qb F)) : LaurentSeries Qb) = coeffMap ιA (f : LaurentSeries L) := rfl

theorem emb_injective : Function.Injective (emb F ιA) := fun _ _ h =>
  Subtype.ext (coeffMap_injective ιA (congrArg Subtype.val h))

theorem emb_algebraMap (l : L) :
    emb F ιA (algebraMap L _ l) = algebraMap Qb (↥(laurentBaseChange Qb F)) (ιA l) :=
  Subtype.ext (coeffMap_algebraMap' ιA l)

theorem arithmeticGalois_smul_emb (τ : Qb ≃ₐ[ℚ] Qb) (hτ : ∀ x : L, τ (ιA x) = ιA x)
    (f : ↥(laurentBaseChange L F)) :
    arithmeticGalois F τ • emb F ιA f = emb F ιA f := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul, coe_emb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun x => hτ x) _

end Emb

section Span

variable (F : IntermediateField ℚ (LaurentSeries ℚ))

theorem mem_span_coeffEmb_of_mem {g : LaurentSeries Qb} (hg : g ∈ laurentBaseChange Qb F) :
    g ∈ Submodule.span Qb (⇑(coeffEmb Qb) '' (F : Set (LaurentSeries ℚ))) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : CharZero (LaurentSeries Qb) :=
    (RingHom.charZero_iff (HahnSeries.C_injective (Γ := ℤ) (R := Qb))).mp inferInstance
  let F' : Subfield (LaurentSeries Qb) := F.toSubfield.map (coeffEmb Qb)
  haveI : CharZero F' := F'.subtype.charZero
  let M' : IntermediateField F' (LaurentSeries Qb) :=
    IntermediateField.adjoin F' (Set.range (algebraMap Qb (LaurentSeries Qb)))

  have hgM : g ∈ M' := by
    have hle : (laurentBaseChange Qb F).toSubfield ≤ M'.toSubfield := by
      rw [laurentBaseChange, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro y (⟨k, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact IntermediateField.subset_adjoin F' _ ⟨k, rfl⟩
      · have hz' : coeffEmb Qb z ∈ F' := Subfield.mem_map.mpr ⟨z, hz, rfl⟩
        exact M'.algebraMap_mem ⟨coeffEmb Qb z, hz'⟩
    exact hle hg

  have halg : ∀ x ∈ Set.range (algebraMap Qb (LaurentSeries Qb)), IsAlgebraic F' x := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨p, hp0, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k)
    refine ⟨p.map (algebraMap ℚ F'), (Polynomial.map_ne_zero_iff (algebraMap ℚ F').injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap F' (LaurentSeries Qb)).comp (algebraMap ℚ F') =
        (algebraMap Qb (LaurentSeries Qb)).comp (algebraMap ℚ Qb) from RingHom.ext_rat _ _,
      ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
  have hM' : M'.toSubalgebra = Algebra.adjoin F' (Set.range (algebraMap Qb (LaurentSeries Qb))) :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
  have hgS : g ∈ Subalgebra.toSubmodule (Algebra.adjoin F' (Set.range (algebraMap Qb (LaurentSeries Qb)))) := by
    change g ∈ Algebra.adjoin F' (Set.range (algebraMap Qb (LaurentSeries Qb)))
    rw [← hM']
    exact hgM
  rw [Algebra.adjoin_eq_span,
    show Set.range (algebraMap Qb (LaurentSeries Qb)) =
      ((algebraMap Qb (LaurentSeries Qb)).rangeS.toSubmonoid : Set (LaurentSeries Qb)) from rfl,
    Submonoid.closure_eq] at hgS
  change g ∈ Submodule.span F' (Set.range (algebraMap Qb (LaurentSeries Qb))) at hgS
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hgS
  rw [← hc]
  refine Submodule.sum_mem _ fun k _ => ?_

  obtain ⟨z, hz, hza⟩ := Subfield.mem_map.mp (c k).2
  change (c k) • algebraMap Qb (LaurentSeries Qb) k ∈ _
  rw [Algebra.smul_def, Subfield.algebraMap_ofSubfield, Subfield.coe_subtype, ← hza, mul_comm,
    algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]
  exact Submodule.smul_mem _ k (Submodule.subset_span ⟨z, hz, rfl⟩)

end Span

section Fixed

variable {L : Type} [Field L] [CharZero L] (ιA : L →+* Qb)

theorem exists_eq_of_forall_fix {c : Qb}
    (hc : ∀ τ : Qb ≃ₐ[ℚ] Qb, (∀ x : L, τ (ιA x) = ιA x) → τ c = c) : ∃ l : L, ιA l = c := by
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : Normal ℚ Qb := @IsAlgClosure.normal ℚ Qb _ _ (AlgebraicClosure.instAlgebra ℚ) _
  haveI : Algebra.IsSeparable ℚ Qb := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ Qb := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  set E : IntermediateField ℚ Qb := (ιA.toRatAlgHom).fieldRange with hE
  have hmem : c ∈ IntermediateField.fixedField E.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hτ
    exact hc τ (fun x => hτ (ιA x) ⟨x, rfl⟩)
  rw [InfiniteGalois.fixedField_fixingSubgroup E, hE, AlgHom.mem_fieldRange] at hmem
  exact hmem

end Fixed

section Descent

variable (F : IntermediateField ℚ (LaurentSeries ℚ)) {L : Type} [Field L] [CharZero L]
  (ιA : L →+* Qb)

theorem smul_coeffEmb_mem {L' : Type} [Field L'] [CharZero L'] (a : L') {y : LaurentSeries ℚ} (hy : y ∈ F) :
    a • coeffEmb L' y ∈ laurentBaseChange L' F := by
  rw [← HahnSeries.single_zero_mul_eq_smul, ← algebraMap_laurentSeries_eq_single]
  exact mul_mem ((laurentBaseChange L' F).algebraMap_mem a) (coeffEmb_mem_laurentBaseChange L' hy)

theorem exists_eq_emb_of_forall_smul_eq (g : ↥(laurentBaseChange Qb F))
    (hg : ∀ τ : Qb ≃ₐ[ℚ] Qb, (∀ x : L, τ (ιA x) = ιA x) → arithmeticGalois F τ • g = g) :
    ∃ f : ↥(laurentBaseChange L F), emb F ιA f = g := by
  classical

  obtain ⟨B, hBF, hBspan, hBli⟩ := exists_linearIndependent ℚ (F : Set (LaurentSeries ℚ))
  let u : B → LaurentSeries Qb := fun x => coeffEmb Qb (x : LaurentSeries ℚ)
  have hu : LinearIndependent Qb u := ModularCurve.linearIndependent_coeffEmb_of_linearIndependent Qb hBli

  have hspan : (g : LaurentSeries Qb) ∈ Submodule.span Qb (Set.range u) := by
    refine (Submodule.span_le.mpr ?_) (mem_span_coeffEmb_of_mem F g.2)
    rintro _ ⟨y, hy, rfl⟩
    have hyB : y ∈ Submodule.span ℚ (Set.range (fun x : B => (x : LaurentSeries ℚ))) := by
      rw [Subtype.range_coe, hBspan]
      exact Submodule.subset_span hy
    obtain ⟨r, hr⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hyB
    rw [← hr, map_finsuppSum, Finsupp.sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [show coeffEmb Qb ((r x) • (x : LaurentSeries ℚ)) = algebraMap ℚ Qb (r x) • u x from
      coeffMap_smul (algebraMap ℚ Qb) (r x) (x : LaurentSeries ℚ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan

  have hfix : ∀ (τ : Qb ≃ₐ[ℚ] Qb), (∀ x : L, τ (ιA x) = ιA x) → ∀ i, τ (d i) = d i := by
    intro τ hτ i
    have hgτ : coeffMap (τ : Qb →+* Qb) (g : LaurentSeries Qb) = g := by
      rw [← coe_arithmeticGalois_smul, hg τ hτ]
    have hsum : (Finsupp.mapRange τ (map_zero τ) d).sum (fun i a => a • u i) =
        d.sum (fun i a => a • u i) := by
      rw [Finsupp.sum_mapRange_index (fun i => zero_smul Qb (u i)), hd, ← hgτ, ← hd, map_finsuppSum]
      refine Finsupp.sum_congr fun i _ => ?_
      change τ (d i) • u i = coeffMap (τ : Qb →+* Qb) (d i • u i)
      rw [coeffMap_smul, coeffMap_coeffEmb]
      rfl
    have hinj := hu (show Finsupp.linearCombination Qb u (Finsupp.mapRange τ (map_zero τ) d) =
        Finsupp.linearCombination Qb u d by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, hsum])
    have := DFunLike.congr_fun hinj i
    rwa [Finsupp.mapRange_apply] at this

  have hl : ∀ i, ∃ l : L, ιA l = d i := fun i => exists_eq_of_forall_fix ιA (fun τ hτ => hfix τ hτ i)
  choose l hl using hl

  refine ⟨⟨∑ i ∈ d.support, l i • coeffEmb L (i : LaurentSeries ℚ), ?_⟩, ?_⟩
  · exact sum_mem fun i _ => smul_coeffEmb_mem F (l i) (hBF i.2)
  · apply Subtype.ext
    rw [coe_emb, map_sum, ← hd, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change coeffMap ιA (l i • coeffEmb L (i : LaurentSeries ℚ)) = d i • u i
    rw [coeffMap_smul, coeffMap_coeffEmb', hl]

end Descent

section Aut

variable (F : IntermediateField ℚ (LaurentSeries ℚ)) {L : Type} [Field L] [CharZero L]
  (ιA : L →+* Qb)
  (ψ : ↥(laurentBaseChange Qb F) ≃ₐ[Qb] ↥(laurentBaseChange Qb F))
  (hψ : ∀ τ : Qb ≃ₐ[ℚ] Qb, (∀ x : L, τ (ιA x) = ιA x) →
      ∀ g : ↥(laurentBaseChange Qb F), ψ (arithmeticGalois F τ • g) = arithmeticGalois F τ • ψ g)

include hψ in
theorem exists_unique_descend (f : ↥(laurentBaseChange L F)) :
    ∃ f' : ↥(laurentBaseChange L F), emb F ιA f' = ψ (emb F ιA f) := by
  obtain ⟨f', hf'⟩ := exists_eq_emb_of_forall_smul_eq F ιA (ψ (emb F ιA f)) (fun τ hτ => by
    rw [← hψ τ hτ, arithmeticGalois_smul_emb F ιA τ hτ])
  exact ⟨f', hf'⟩

def descendFun (f : ↥(laurentBaseChange L F)) : ↥(laurentBaseChange L F) :=
  Classical.choose (exists_unique_descend F ιA ψ hψ f)

theorem emb_descendFun (f : ↥(laurentBaseChange L F)) :
    emb F ιA (descendFun F ιA ψ hψ f) = ψ (emb F ιA f) :=
  Classical.choose_spec (exists_unique_descend F ιA ψ hψ f)

def descend : ↥(laurentBaseChange L F) →ₐ[L] ↥(laurentBaseChange L F) where
  toFun := descendFun F ιA ψ hψ
  map_one' := emb_injective F ιA (by rw [emb_descendFun]; simp)
  map_mul' f g := emb_injective F ιA (by rw [emb_descendFun, map_mul, map_mul, map_mul, emb_descendFun, emb_descendFun])
  map_zero' := emb_injective F ιA (by rw [emb_descendFun]; simp)
  map_add' f g := emb_injective F ιA (by rw [emb_descendFun, map_add, map_add, map_add, emb_descendFun, emb_descendFun])
  commutes' l := emb_injective F ιA (by rw [emb_descendFun, emb_algebraMap, AlgEquiv.commutes])

@[scoped simp] theorem emb_descend (f : ↥(laurentBaseChange L F)) :
    emb F ιA (descend F ιA ψ hψ f) = ψ (emb F ιA f) := emb_descendFun F ιA ψ hψ f

end Aut

end W0A
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm.W0A"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm.W0A"

open W0A ModularCurve in
theorem solution
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (L : Type) [Field L] [CharZero L] (ιA : L →+* AlgebraicClosure ℚ)
    (θ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F) ≃ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F))
    (hθgal : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x : L, τ (ιA x) = ιA x) →
        ∀ g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F),
          θ (arithmeticGalois F τ • g) = arithmeticGalois F τ • θ g) :
    ∃ σ : ↥(laurentBaseChange L F) ≃ₐ[L] ↥(laurentBaseChange L F),
      ∀ (f : ↥(laurentBaseChange L F)) (g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F)),
        (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap ιA (f : LaurentSeries L) →
          ((θ g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffMap ιA ((σ f : ↥(laurentBaseChange L F)) : LaurentSeries L) := by

  have hθ' : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x : L, τ (ιA x) = ιA x) →
      ∀ g : ↥(laurentBaseChange (AlgebraicClosure ℚ) F),
        θ.symm (arithmeticGalois F τ • g) = arithmeticGalois F τ • θ.symm g := by
    intro τ hτ g
    apply θ.injective
    rw [AlgEquiv.apply_symm_apply, hθgal τ hτ, AlgEquiv.apply_symm_apply]
  let d := descend F ιA θ hθgal
  let d' := descend F ιA θ.symm hθ'
  have h₁ : d.comp d' = AlgHom.id L _ := by
    refine AlgHom.ext fun f => ?_
    apply emb_injective F ιA
    change emb F ιA (d (d' f)) = emb F ιA f
    rw [emb_descend, emb_descend, AlgEquiv.apply_symm_apply]
  have h₂ : d'.comp d = AlgHom.id L _ := by
    refine AlgHom.ext fun f => ?_
    apply emb_injective F ιA
    change emb F ιA (d' (d f)) = emb F ιA f
    rw [emb_descend, emb_descend, AlgEquiv.symm_apply_apply]
  refine ⟨AlgEquiv.ofAlgHom d d' h₁ h₂, fun f g hfg => ?_⟩
  have hg : g = emb F ιA f := Subtype.ext hfg
  subst hg
  change ((θ (emb F ιA f) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F)) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffMap ιA ((d f : ↥(laurentBaseChange L F)) : LaurentSeries L)
  rw [← coe_emb F ιA (d f), emb_descend]

end S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm (solution)
