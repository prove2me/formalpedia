-- Prove2me | solution 1 for NumberField.LevelArith.exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9b8207f9-a1ee-5782-8ecb-32ad5ffd4e47

import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory IsDedekindDomain NumberField NumberField.LevelArith ExtCitation
open scoped NumberField.LevelArith NumberField.InfPlaceDecomp ComplexConjugate

noncomputable section

local instance isAlgebraicQbar_al : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_al : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_al : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace P2MArchLoc

local notation "ℚb" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma eq_one_or_eq_of_mem_archimedeanDecomposition {g : Γ} (hg : g ∈ archimedeanDecomposition) :
    g = 1 ∨ g = complexConjugation := by
  let H : Subgroup Γ :=
    { carrier := {g | g = 1 ∨ g = complexConjugation}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (one_mul _)
        · exact Or.inr (one_mul _)
        · exact Or.inr (mul_one _)
        · exact Or.inl complexConjugation_mul_self
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl inv_one
        · exact Or.inr complexConjugation_inv }
  have hle : archimedeanDecomposition ≤ H := (Subgroup.zpowers_le (H := H)).2 (Or.inr rfl)
  exact hle hg

lemma coe_eq_one_or (g : ↥archimedeanDecomposition) : (g : Γ) = 1 ∨ (g : Γ) = complexConjugation :=
  eq_one_or_eq_of_mem_archimedeanDecomposition g.2

lemma eq_one_or_eq_gen (g : ↥archimedeanDecomposition) : g = 1 ∨ g = archimedeanGen := by
  rcases coe_eq_one_or g with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

local instance instAlgebraQbarComplex_al : Algebra ℚb ℂ := complexEmbedding.toRingHom.toAlgebra

local instance instTowerQbarComplex_al : IsScalarTower ℚ ℚb ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

lemma algebraMap_qbar_complex (z : ℚb) : algebraMap ℚb ℂ z = complexEmbedding z := rfl

lemma exists_aut_forall_complexEmbedding_eq (K : Type) [Field K] [Algebra ℚ K] [Algebra K ℚb] [IsScalarTower ℚ K ℚb]
    (φ : K →+* ℂ) :
    ∃ ρ : Γ, ∀ x : K, complexEmbedding (ρ (algebraMap K ℚb x)) = φ x := by
  letI : Algebra K ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic K ℚb := Algebra.IsAlgebraic.tower_top (K := ℚ) (L := K) (A := ℚb)
  let ψ : ℚb →ₐ[K] ℂ := IsAlgClosed.lift
  have hψ : ∀ x : K, ψ (algebraMap K ℚb x) = φ x := fun x => ψ.commutes x
  let ψℚ : ℚb →ₐ[ℚ] ℂ :=
    { toRingHom := ψ.toRingHom
      commutes' := fun r => by
        change ψ.toRingHom (algebraMap ℚ ℚb r) = algebraMap ℚ ℂ r
        rw [eq_ratCast (algebraMap ℚ ℚb), eq_ratCast (algebraMap ℚ ℂ), map_ratCast] }
  refine ⟨ψℚ.restrictNormal' ℚb, fun x => ?_⟩
  have h := AlgHom.restrictNormal_commutes ψℚ ℚb (algebraMap K ℚb x)
  rw [algebraMap_qbar_complex, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [← hψ x]
  exact h

section Completion

variable {E K : Type*} [Field E] [Field K] [Algebra E K] {w : InfinitePlace K}

lemma extensionEmbedding_algebraMap (x : K) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap K w.Completion x) = w.embedding x := by
  change InfinitePlace.Completion.extensionEmbedding w (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) = _
  rw [InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply]

lemma extensionEmbedding_smul_of_isConj (τ : ↥(NumberField.InfPlaceDecomp.decomp E K w))
    (hτ : ComplexEmbedding.IsConj w.embedding (τ : K ≃ₐ[E] K)) (z : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w (τ • z) = conj (InfinitePlace.Completion.extensionEmbedding w z) := by
  induction z using InfinitePlace.Completion.induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        ((NumberField.InfPlaceDecomp.continuous_actRingEquiv τ).congr fun z =>
          (NumberField.InfPlaceDecomp.smul_def τ z).symm)
    · exact Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  | ih a =>
    rw [NumberField.InfPlaceDecomp.smul_def, NumberField.InfPlaceDecomp.actRingEquiv_coe,
      InfinitePlace.Completion.extensionEmbedding_coe, InfinitePlace.Completion.extensionEmbedding_coe,
      WithAbs.congr_apply]
    change w.embedding ((τ : K ≃ₐ[E] K) (WithAbs.equiv w.1 a)) = _
    exact hτ.eq _

end Completion

variable (L F : IntermediateField ℚ ℚb) (hLF : L ≤ F)
variable [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]

set_option hygiene false in
local notation "Kf" => ↥(levelField L F hLF)

lemma coe_mem_F (x : Kf) : (x : ℚb) ∈ F := (IntermediateField.mem_extendScalars hLF).1 x.2

lemma coe_levelGal (γ : ↥L.fixingSubgroup) (x : Kf) : ((levelGal L F hLF γ x : Kf) : ℚb) = (γ : Γ) (x : ℚb) :=
  levelGal_apply_coe L F hLF γ x

set_option maxHeartbeats 32000000 in

theorem main' (T : Finset (HeightOneSpectrum (𝓞 ↥L)))
    (f : groupCohomology.cocycles₂ (NumberField.SUnits.sUnitsRep ↥L Kf T))
    (w : InfinitePlace Kf)
    (hyp : ∀ (σ : Γ) (hσ : ∀ g : ↥archimedeanDecomposition, σ * (g : Γ) * σ⁻¹ ∈ L.fixingSubgroup),
      ∃ c₁ : ↥archimedeanDecomposition → Additive ℚbˣ, ∀ g h : ↥archimedeanDecomposition,
        Additive.ofMul (Units.map (algebraMap Kf ℚb).toMonoidHom
            (NumberField.SUnits.val ↥L Kf T (f (levelGal L F hLF ⟨σ * (g : Γ) * σ⁻¹, hσ g⟩, levelGal L F hLF ⟨σ * (h : Γ) * σ⁻¹, hσ h⟩)))) =
          Additive.ofMul ((σ * (g : Γ) * σ⁻¹) • Additive.toMul (c₁ h)) - c₁ (g * h) + c₁ g) :
    ∃ y : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w) → Additive (w.Completion)ˣ,
      ∀ a b : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w),
        Additive.ofMul (Units.map (algebraMap Kf w.Completion).toMonoidHom
            (NumberField.SUnits.val ↥L Kf T (f ((a : Kf ≃ₐ[↥L] Kf), (b : Kf ≃ₐ[↥L] Kf))))) =
          Additive.ofMul (a • (Additive.toMul (y b) : (w.Completion)ˣ)) - y (a * b) + y a := by

  obtain ⟨A, hA⟩ : ∃ A : (Kf ≃ₐ[↥L] Kf) → (Kf ≃ₐ[↥L] Kf) → Additive (w.Completion)ˣ, ∀ a b : Kf ≃ₐ[↥L] Kf,
      Additive.ofMul (Units.map (algebraMap Kf w.Completion).toMonoidHom (NumberField.SUnits.val ↥L Kf T (f (a, b)))) = A a b :=
    ⟨fun a b => Additive.ofMul (Units.map (algebraMap Kf w.Completion).toMonoidHom (NumberField.SUnits.val ↥L Kf T (f (a, b)))),
      fun _ _ => rfl⟩
  simp only [hA]
  by_cases hunr : w.IsUnramified ↥L
  ·
    have hbot : NumberField.InfPlaceDecomp.decomp ↥L Kf w = ⊥ := hunr.stabilizer_eq_bot
    have hone : ∀ a : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w), a = 1 := fun a =>
      Subtype.ext ((Subgroup.mem_bot).1 (hbot ▸ a.2))
    refine ⟨fun _ => A 1 1, fun a b => ?_⟩
    rw [hone a, hone b, one_smul, mul_one, ofMul_toMul]
    change A 1 1 = A 1 1 - A 1 1 + A 1 1
    abel

  obtain ⟨hwC, hvR⟩ := (InfinitePlace.not_isUnramified_iff).1 hunr
  have hmkφ : InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding w

  obtain ⟨ρ, hρ⟩ := exists_aut_forall_complexEmbedding_eq Kf w.embedding
  have hρ' : ∀ x : Kf, complexEmbedding (ρ (x : ℚb)) = w.embedding x := fun x => hρ x

  have hconjρ : ∀ (g : Γ) (z : ℚb), ρ ((ρ⁻¹ * g * (ρ⁻¹)⁻¹) z) = g (ρ z) := by
    intro g z
    rw [← AlgEquiv.mul_apply, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, AlgEquiv.mul_apply]
  have hcc : ∀ z : ℚb, complexEmbedding (complexConjugation z) = conj (complexEmbedding z) :=
    complexEmbedding_complexConjugation

  have hreal : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap ↥L Kf)) := by
    rw [← hmkφ, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff] at hvR
    exact hvR
  have hσmem : ∀ g : ↥archimedeanDecomposition, ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹ ∈ L.fixingSubgroup := by
    intro g
    rcases coe_eq_one_or g with hg | hg
    · rw [hg, mul_one, mul_inv_cancel]; exact one_mem _
    rw [hg, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply ρ.injective
    apply complexEmbedding.toRingHom.injective
    change complexEmbedding (ρ ((ρ⁻¹ * complexConjugation * (ρ⁻¹)⁻¹) y)) = complexEmbedding (ρ y)
    rw [hconjρ, hcc]
    have h1 : complexEmbedding (ρ y) = w.embedding (algebraMap ↥L Kf ⟨y, hy⟩) := hρ' (algebraMap ↥L Kf ⟨y, hy⟩)
    rw [h1]
    have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hreal) ⟨y, hy⟩
    rw [ComplexEmbedding.conjugate_coe_eq] at h2
    exact h2

  obtain ⟨c₁, hc₁⟩ := hyp ρ⁻¹ hσmem

  obtain ⟨θ, hθ⟩ : ∃ θ : w.Completion ≃+* ℂ, ∀ z, θ z = InfinitePlace.Completion.extensionEmbedding w z :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC, fun _ => rfl⟩
  obtain ⟨e, hθe⟩ : ∃ e : ℚb →+* w.Completion, ∀ u : ℚb, θ (e u) = complexEmbedding (ρ u) :=
    ⟨θ.symm.toRingHom.comp (complexEmbedding.toRingHom.comp ρ.toAlgHom.toRingHom), fun u => RingEquiv.apply_symm_apply θ _⟩

  obtain ⟨r, hr⟩ : ∃ r : ↥archimedeanDecomposition → (Kf ≃ₐ[↥L] Kf),
      ∀ g : ↥archimedeanDecomposition, levelGal L F hLF ⟨ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹, hσmem g⟩ = r g :=
    ⟨fun g => levelGal L F hLF ⟨ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹, hσmem g⟩, fun _ => rfl⟩
  have hφr : ∀ (g : ↥archimedeanDecomposition) (x : Kf),
      w.embedding (r g x) = complexEmbedding ((g : Γ) (ρ (x : ℚb))) := by
    intro g x
    rw [← hρ', ← hr, coe_levelGal]
    change complexEmbedding (ρ ((ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹) (x : ℚb))) = _
    rw [hconjρ]
  have hr1 : r 1 = 1 := by
    rw [← hr]
    have : (⟨ρ⁻¹ * ((1 : ↥archimedeanDecomposition) : Γ) * (ρ⁻¹)⁻¹, hσmem 1⟩ : ↥L.fixingSubgroup) = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one]
  have hrmul : ∀ g h : ↥archimedeanDecomposition, r (g * h) = r g * r h := by
    intro g h
    rw [← hr, ← hr, ← hr, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  have hconj : ComplexEmbedding.IsConj w.embedding (r archimedeanGen) := by
    refine RingHom.ext fun x => ?_
    rw [ComplexEmbedding.conjugate_coe_eq]
    change conj (w.embedding x) = w.embedding (r archimedeanGen x)
    rw [hφr, ← hρ' x]
    exact (hcc _).symm
  have hτ₀ne : r archimedeanGen ≠ 1 := by
    rw [ComplexEmbedding.isConj_ne_one_iff hconj, ← InfinitePlace.isReal_iff, InfinitePlace.not_isReal_iff_isComplex]
    exact hwC

  have hmemD : r archimedeanGen ∈ NumberField.InfPlaceDecomp.decomp ↥L Kf w := by
    have := (InfinitePlace.mem_stabilizer_mk_iff w.embedding (r archimedeanGen)).2 (Or.inr hconj)
    rwa [hmkφ] at this
  have hDcases : ∀ a : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w),
      (a : Kf ≃ₐ[↥L] Kf) = 1 ∨ (a : Kf ≃ₐ[↥L] Kf) = r archimedeanGen := by
    intro a
    have ha : (a : Kf ≃ₐ[↥L] Kf) ∈ (MulAction.stabilizer (Kf ≃ₐ[↥L] Kf) (InfinitePlace.mk w.embedding) : Set (Kf ≃ₐ[↥L] Kf)) := by
      rw [hmkφ]; exact a.2
    rw [hconj.coe_stabilizer_mk] at ha
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  have hmemr : ∀ g : ↥archimedeanDecomposition, r g ∈ NumberField.InfPlaceDecomp.decomp ↥L Kf w := by
    intro g
    rcases eq_one_or_eq_gen g with hg | hg
    · rw [hg, hr1]; exact one_mem _
    · rw [hg]; exact hmemD
  obtain ⟨rD, hrD⟩ : ∃ rD : ↥archimedeanDecomposition → ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w),
      ∀ g : ↥archimedeanDecomposition, ((rD g : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w)) : Kf ≃ₐ[↥L] Kf) = r g :=
    ⟨fun g => ⟨r g, hmemr g⟩, fun _ => rfl⟩
  have hrD1 : rD 1 = 1 := Subtype.ext ((hrD 1).trans hr1)
  have hrDmul : ∀ g h : ↥archimedeanDecomposition, rD (g * h) = rD g * rD h := fun g h =>
    Subtype.ext (by rw [Subgroup.coe_mul, hrD, hrD, hrD]; exact hrmul g h)
  have hconjD : ComplexEmbedding.IsConj w.embedding
      ((rD archimedeanGen : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w)) : Kf ≃ₐ[↥L] Kf) := by
    rw [hrD]; exact hconj

  have hE1 : ∀ x : Kf, e (x : ℚb) = algebraMap Kf w.Completion x := by
    intro x
    apply θ.injective
    have h3 : θ (algebraMap Kf w.Completion x) = w.embedding x := (hθ _).trans (extensionEmbedding_algebraMap x)
    exact ((hθe _).trans (hρ' x)).trans h3.symm
  have hE2one : ∀ u : ℚb, e ((ρ⁻¹ * ((1 : ↥archimedeanDecomposition) : Γ) * (ρ⁻¹)⁻¹) u) = rD 1 • e u := by
    intro u
    rw [hrD1, one_smul, OneMemClass.coe_one, mul_one, mul_inv_cancel, AlgEquiv.one_apply]
  have hE2gen : ∀ u : ℚb, e ((ρ⁻¹ * ((archimedeanGen : ↥archimedeanDecomposition) : Γ) * (ρ⁻¹)⁻¹) u) =
      rD archimedeanGen • e u := by
    intro u
    apply θ.injective
    rw [hθ, hθ, extensionEmbedding_smul_of_isConj (rD archimedeanGen) hconjD, ← hθ, ← hθ, hθe, hθe, hconjρ]
    exact hcc _
  have hE2 : ∀ (g : ↥archimedeanDecomposition) (u : ℚb), e ((ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹) u) = rD g • e u := by
    intro g
    rcases eq_one_or_eq_gen g with hg | hg
    · rw [hg]; exact hE2one
    · rw [hg]; exact hE2gen

  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Additive ℚbˣ →+ Additive (w.Completion)ˣ, ∀ u : ℚbˣ,
      Θ (Additive.ofMul u) = Additive.ofMul (Units.map e.toMonoidHom u) :=
    ⟨MonoidHom.toAdditive (Units.map e.toMonoidHom), fun _ => rfl⟩
  have hΘval : ∀ a b : Kf ≃ₐ[↥L] Kf,
      Θ (Additive.ofMul (Units.map (algebraMap Kf ℚb).toMonoidHom (NumberField.SUnits.val ↥L Kf T (f (a, b))))) = A a b := by
    intro a b
    rw [hΘ, ← hA]
    have h4 : Units.map e.toMonoidHom (Units.map (algebraMap Kf ℚb).toMonoidHom (NumberField.SUnits.val ↥L Kf T (f (a, b)))) =
        Units.map (algebraMap Kf w.Completion).toMonoidHom (NumberField.SUnits.val ↥L Kf T (f (a, b))) :=
      Units.ext (hE1 _)
    rw [h4]
  have hΘsmul : ∀ (g : ↥archimedeanDecomposition) (u : ℚbˣ),
      Θ (Additive.ofMul ((ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹) • u)) = Additive.ofMul (rD g • Units.map e.toMonoidHom u) := by
    intro g u
    rw [hΘ]
    have h2 : Units.map e.toMonoidHom ((ρ⁻¹ * (g : Γ) * (ρ⁻¹)⁻¹) • u) = rD g • Units.map e.toMonoidHom u :=
      Units.ext (hE2 g u)
    rw [h2]

  have key : ∀ g h : ↥archimedeanDecomposition,
      A (r g) (r h) = Additive.ofMul (rD g • (Additive.toMul (Θ (c₁ h)) : (w.Completion)ˣ)) - Θ (c₁ (g * h)) + Θ (c₁ g) := by
    intro g h
    have h1 := congrArg Θ (hc₁ g h)
    rw [map_add Θ, map_sub Θ, hr, hr, hΘval] at h1
    rw [h1]
    congr 2
    rw [← ofMul_toMul (c₁ h), hΘsmul, toMul_ofMul, hΘ, toMul_ofMul]

  obtain ⟨s, hs1, hs2⟩ : ∃ s : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w) → ↥archimedeanDecomposition,
      (∀ a : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w), (a : Kf ≃ₐ[↥L] Kf) = 1 → s a = 1) ∧
        (∀ a : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf w), (a : Kf ≃ₐ[↥L] Kf) ≠ 1 → s a = archimedeanGen) := by
    classical
    exact ⟨fun a => if (a : Kf ≃ₐ[↥L] Kf) = 1 then 1 else archimedeanGen, fun a ha => if_pos ha, fun a ha => if_neg ha⟩
  have hs : ∀ a, rD (s a) = a := by
    intro a
    rcases hDcases a with ha | ha
    · rw [hs1 a ha, hrD1]
      exact Subtype.ext ha.symm
    · rw [hs2 a (by rw [ha]; exact hτ₀ne)]
      exact Subtype.ext ((hrD _).trans ha.symm)
  have hsrD : ∀ g, s (rD g) = g := by
    intro g
    rcases eq_one_or_eq_gen g with hg | hg
    · rw [hg]; exact hs1 _ ((hrD 1).trans hr1)
    · rw [hg]; exact hs2 _ (by rw [hrD]; exact hτ₀ne)
  refine ⟨fun a => Θ (c₁ (s a)), fun a b => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, rD g = a := ⟨s a, hs a⟩
  obtain ⟨h, rfl⟩ : ∃ h, rD h = b := ⟨s b, hs b⟩
  show A (rD g) (rD h) = Additive.ofMul (rD g • (Additive.toMul (Θ (c₁ (s (rD h)))) : (w.Completion)ˣ)) -
    Θ (c₁ (s (rD g * rD h))) + Θ (c₁ (s (rD g)))
  rw [← hrDmul, hsrD, hsrD, hsrD, hrD, hrD]
  exact key g h

theorem main (T : Finset (HeightOneSpectrum (𝓞 ↥L)))
    (f : groupCohomology.cocycles₂ (NumberField.SUnits.sUnitsRep ↥L Kf T))
    (v : InfinitePlace ↥L)
    (hyp : ∀ (σ : Γ) (hσ : ∀ g : ↥archimedeanDecomposition, σ * (g : Γ) * σ⁻¹ ∈ L.fixingSubgroup),
      ∃ c₁ : ↥archimedeanDecomposition → Additive ℚbˣ, ∀ g h : ↥archimedeanDecomposition,
        Additive.ofMul (Units.map (algebraMap Kf ℚb).toMonoidHom
            (NumberField.SUnits.val ↥L Kf T (f (levelGal L F hLF ⟨σ * (g : Γ) * σ⁻¹, hσ g⟩, levelGal L F hLF ⟨σ * (h : Γ) * σ⁻¹, hσ h⟩)))) =
          Additive.ofMul ((σ * (g : Γ) * σ⁻¹) • Additive.toMul (c₁ h)) - c₁ (g * h) + c₁ g) :
    ∃ y : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf (NumberField.ArchIdele.above ↥L Kf v)) →
        NumberField.InfPlaceDecomp.localUnits ↥L Kf (NumberField.ArchIdele.above ↥L Kf v),
      ∀ a b : ↥(NumberField.InfPlaceDecomp.decomp ↥L Kf (NumberField.ArchIdele.above ↥L Kf v)),
        Additive.ofMul (Units.map (NumberField.SIdele.locInf ↥L Kf v).toMonoidHom
            (NumberField.SUnits.val ↥L Kf T (f ((a : Kf ≃ₐ[↥L] Kf), (b : Kf ≃ₐ[↥L] Kf))))) =
          (NumberField.InfPlaceDecomp.localUnits ↥L Kf (NumberField.ArchIdele.above ↥L Kf v)).ρ a (y b) - y (a * b) + y a :=
  main' L F hLF T f (NumberField.ArchIdele.above ↥L Kf v) hyp

end P2MArchLoc

end

theorem solution
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (T : Finset (HeightOneSpectrum (𝓞 ↥L)))
    (f : groupCohomology.cocycles₂ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) T))
    (v : InfinitePlace ↥L)
    (hyp : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (hσ : ∀ g : ↥archimedeanDecomposition,
        σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹ ∈ L.fixingSubgroup),
      ∃ c₁ : ↥archimedeanDecomposition → Additive (AlgebraicClosure ℚ)ˣ, ∀ g h : ↥archimedeanDecomposition,
        Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) (AlgebraicClosure ℚ)).toMonoidHom
            (NumberField.SUnits.val ↥L ↥(levelField L F hLF) T
              (f (levelGal L F hLF ⟨σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹, hσ g⟩,
                  levelGal L F hLF ⟨σ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹, hσ h⟩)))) =
          Additive.ofMul ((σ * (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ⁻¹) • Additive.toMul (c₁ h))
            - c₁ (g * h) + c₁ g) :
    ∃ y : ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF)
          (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)) →
        NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v),
      ∀ a b : ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)),
        Additive.ofMul (Units.map (NumberField.SIdele.locInf ↥L ↥(levelField L F hLF) v).toMonoidHom
            (NumberField.SUnits.val ↥L ↥(levelField L F hLF) T
              (f ((a : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)),
                  (b : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)))))) =
          (NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF)
              (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)).ρ a (y b) - y (a * b) + y a :=
  P2MArchLoc.main L F hLF T f v hyp

end S_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition
end P2MW
export P2MW.S_NumberField_LevelArith_exists_coboundary_localUnits_infinitePlace_of_forall_conj_archimedeanDecomposition (solution)
