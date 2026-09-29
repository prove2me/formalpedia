-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_hom_lift_nsmul_pow_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/58d8e396-ae74-5f80-abaf-f7bfacaa5092

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_lift_nsmul_pow_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped TensorProduct

namespace KB1Asm

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp ψ hψ P) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
      change schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n P) P) =
        L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ P)) (schemeHomOverComp ψ hψ P)
      rw [L.mul_natural, ih]

theorem mapPt_schemeHomOverComp {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    mapPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (Category.assoc _ _ _)

theorem SchemeHomOver.ext_of_cover {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (𝒰 : T.OpenCover)
    (P Q : SchemeHomOver t f)
    (h : ∀ i, schemeHomOverComp (𝒰.f i) rfl P = schemeHomOverComp (𝒰.f i) (rfl : 𝒰.f i ≫ t = 𝒰.f i ≫ t) Q) :
    P = Q :=
  Subtype.ext (𝒰.hom_ext _ _ fun i => by simpa only [schemeHomOverComp_coe] using congrArg Subtype.val (h i))

theorem exists_algebra_eq_specOver (S : CommRingCat.{0}) (t : Spec S ⟶ Spec (CommRingCat.of R)) :
    ∃ inst : Algebra R S, t = @Scheme.specOver R _ S _ inst := by
  refine ⟨(Spec.preimage t).hom.toAlgebra, ?_⟩
  change t = Spec.map (CommRingCat.ofHom (Spec.preimage t).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mapPt_mul_of_affine {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (u : A ⟶ A') (hu : u ≫ f' = f)
    (h : ∀ (C : Type) [CommRing C] [Algebra R C] (P Q : SchemeHomOver (Scheme.specOver (𝒪 := R) C) f),
      mapPt u hu (L.mul _ P Q) = L'.mul _ (mapPt u hu P) (mapPt u hu Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    mapPt u hu (L.mul t P Q) = L'.mul t (mapPt u hu P) (mapPt u hu Q) := by

  have key : ∀ (S : CommRingCat.{0}) (t' : Spec S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' f),
      mapPt u hu (L.mul t' P Q) = L'.mul t' (mapPt u hu P) (mapPt u hu Q) := by
    intro S t' P Q
    obtain ⟨inst, ht'⟩ := exists_algebra_eq_specOver S t'
    subst ht'
    exact @h S _ inst P Q
  refine SchemeHomOver.ext_of_cover T.affineOpenCover.openCover _ _ fun i => ?_
  change schemeHomOverComp (T.affineOpenCover.f i) rfl (mapPt u hu (L.mul t P Q)) =
    schemeHomOverComp (T.affineOpenCover.f i) rfl (L'.mul t (mapPt u hu P) (mapPt u hu Q))
  rw [← mapPt_schemeHomOverComp, L.mul_natural, L'.mul_natural, key, mapPt_schemeHomOverComp,
    mapPt_schemeHomOverComp]

theorem hom_eq_of_affine {Y : Scheme.{0}} (u v : A ⟶ Y)
    (h : ∀ (C : Type) [CommRing C] [Algebra R C] (P : SchemeHomOver (Scheme.specOver (𝒪 := R) C) f),
      P.1 ≫ u = P.1 ≫ v) : u = v := by
  refine A.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  change A.affineOpenCover.f i ≫ u = A.affineOpenCover.f i ≫ v
  obtain ⟨inst, ht⟩ := exists_algebra_eq_specOver (A.affineOpenCover.X i) (A.affineOpenCover.f i ≫ f)
  exact @h _ _ inst ⟨A.affineOpenCover.f i, ht⟩

theorem RelativeGroupLaw.eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem nsmulPt_comp_of_mul_comp {R₀ : Type} [CommRing R₀] (φ : R →+* R₀)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R f) (L₀ : RelativeGroupLaw R₀ f₀) (g : A₀ ⟶ A)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom φ))
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (k : ℕ) (Q : SchemeHomOver t f₀) :
    (nsmulPt L₀ t k Q).1 ≫ g =
      (nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom φ)) k
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, Q.2]⟩).1 := by

  let gpt : SchemeHomOver t f₀ → SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) f :=
    fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
  have hone : gpt (L₀.one t) = L.one _ := by
    apply RelativeGroupLaw.eq_one_of_mul_self
    apply Subtype.ext
    have := hmul t (L₀.one t) (L₀.one t)
    rw [L₀.one_mul] at this
    exact this.symm
  suffices H : ∀ k, gpt (nsmulPt L₀ t k Q) = nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom φ)) k (gpt Q) from
    congrArg Subtype.val (H k)
  intro k
  induction k with
  | zero => exact hone
  | succ k ih =>
      change gpt (L₀.mul t (nsmulPt L₀ t k Q) Q) =
        L.mul _ (nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom φ)) k (gpt Q)) (gpt Q)
      rw [← ih]
      exact Subtype.ext (hmul t _ _)

theorem nsmulPt_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (e : t₁ = t₂) (k : ℕ) (x₁ : SchemeHomOver t₁ f) (x₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) :
    (nsmulPt L t₁ k x₁).1 = (nsmulPt L t₂ k x₂).1 := by
  subst e
  have : x₁ = x₂ := Subtype.ext hx
  subst this
  rfl

section formalHelpers
variable {B : Type} [CommRing B]

theorem map_nilEval {σ : Type} [Fintype σ] [DecidableEq σ] {B' B'' : Type} [CommRing B'] [Algebra B B']
    [CommRing B''] [Algebra B B''] (χ : B' →ₐ[B] B'') (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → B') :
    χ (MvFormalGroup.nilEval n φ a) = MvFormalGroup.nilEval n φ (χ ∘ a) := by
  unfold MvFormalGroup.nilEval
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem constantCoeff_nthSeries {g : ℕ} (F : MvFormalGroup g B) (m : ℕ) (i : Fin g) :
    MvPowerSeries.constantCoeff (F.nthSeries m i) = 0 := by
  induction m generalizing i with
  | zero => simp [MvFormalGroup.nthSeries_zero]
  | succ m ih =>
      rw [MvFormalGroup.nthSeries_succ]
      have h0 : ∀ j : Fin g ⊕ Fin g, MvPowerSeries.constantCoeff (Sum.elim (F.nthSeries m) (fun j => MvPowerSeries.X j) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact MvPowerSeries.constantCoeff_X j
      exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0
        (F.constantCoeff_eq_zero i)

theorem nilEval_nthSeries_of_mem {g : ℕ} (F : MvFormalGroup g B) {B' : Type} [CommRing B'] [Algebra B B']
    (J : Ideal B') (k : ℕ) (hJ : J ^ (k + 1) = ⊥) (u : Fin g → B') (hu : ∀ i, u i ∈ J) (m : ℕ) :
    (∀ i, ((fun t : Fin g → B' => F.nilMul k t u)^[m] 0) i ∈ J) ∧
    ∀ i, MvFormalGroup.nilEval k (F.nthSeries m i) u = ((fun t : Fin g → B' => F.nilMul k t u)^[m] 0) i := by
  induction m with
  | zero =>
      refine ⟨fun i => by simp, fun i => ?_⟩
      simp [MvFormalGroup.nthSeries_zero, MvFormalGroup.nilEval]
  | succ m ih =>
      obtain ⟨ihmem, iheq⟩ := ih
      have hmem : ∀ j : Fin g ⊕ Fin g, Sum.elim ((fun t : Fin g → B' => F.nilMul k t u)^[m] 0) u j ∈ J := by
        rintro (j | j)
        · exact ihmem j
        · exact hu j
      have step : ∀ i, ((fun t : Fin g → B' => F.nilMul k t u)^[m + 1] 0) i =
          MvFormalGroup.nilEval k (F.toPowerSeries i) (Sum.elim ((fun t : Fin g → B' => F.nilMul k t u)^[m] 0) u) := by
        intro i; rw [Function.iterate_succ_apply']; rfl
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [step]
        exact (MvFormalGroup.nilEval_subst_of_mem J k hJ _ hmem (fun _ : Unit => F.toPowerSeries i)
          (fun _ => F.constantCoeff_eq_zero i) 0).1 ()
      · rw [step, MvFormalGroup.nthSeries_succ]
        have h0 : ∀ j : Fin g ⊕ Fin g, MvPowerSeries.constantCoeff (Sum.elim (F.nthSeries m) (fun j => MvPowerSeries.X j) j) = 0 := by
          rintro (j | j)
          · exact constantCoeff_nthSeries F m j
          · exact MvPowerSeries.constantCoeff_X j
        rw [(MvFormalGroup.nilEval_subst_of_mem J k hJ u hu _ h0 (F.toPowerSeries i)).2]
        congr 1
        funext j
        rcases j with j | j
        · exact iheq j
        · exact MvFormalGroup.nilEval_X_of_mem J k hJ u hu j

theorem nsmul_formalCoordinates_eq_iterate {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ) {B' : Type} [CommRing B'] [Algebra B B']
    (J : Ideal B') (k : ℕ) (hJ : J ^ (k + 1) = ⊥) (u : Fin g → B') (hu : ∀ i, u i ∈ J) (m : ℕ) :
    L.nsmul (Scheme.specOver (𝒪 := B) B') m (θ B' u) = θ B' ((fun t : Fin g → B' => F.nilMul k t u)^[m] 0) := by
  obtain ⟨-, hθJ⟩ := hθ
  obtain ⟨-, -, -, hhom⟩ := hθJ B' J k hJ
  have hθ0 : θ B' 0 = L.one (Scheme.specOver (𝒪 := B) B') := by
    obtain ⟨-, -, honto0, -⟩ := hθJ B' ⊥ 0 (by rw [zero_add, pow_one])
    have hone : L.IsInfinitesimal (⊥ : Ideal B') (L.one (Scheme.specOver (𝒪 := B) B')) := L.one_natural _ _ _ _
    obtain ⟨s0, hs0, hθs0⟩ := honto0 _ hone
    have : s0 = 0 := funext fun i => (Submodule.mem_bot B').mp (hs0 i)
    rw [← hθs0, this]
  have hmem := fun m => (nilEval_nthSeries_of_mem F J k hJ u hu m).1
  induction m with
  | zero => rw [RelativeGroupLaw.nsmul_zero, Function.iterate_zero, id_eq, hθ0]
  | succ m ih =>
      rw [RelativeGroupLaw.nsmul_succ, ih, Function.iterate_succ_apply', ← hhom _ _ (hmem m) hu]

end formalHelpers

section reductionHelpers

theorem exists_algebra_quotient_isScalarTower {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (C : Type) [CommRing C] [Algebra B C] :
    ∃ inst : Algebra B₀ (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)),
      @IsScalarTower B B₀ (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)) _ inst.toSMul _ := by
  let I : Ideal B := RingHom.ker (algebraMap B B₀)
  let I' : Ideal C := I.map (algebraMap B C)
  let e : (B ⧸ I) ≃+* B₀ := RingHom.quotientKerEquivOfSurjective hπ
  let χ : B₀ →+* C ⧸ I' := (Ideal.quotientMap I' (algebraMap B C) Ideal.le_comap_map).comp e.symm.toRingHom
  refine ⟨χ.toAlgebra, ?_⟩
  letI : Algebra B₀ (C ⧸ I') := χ.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change Ideal.Quotient.mk I' (algebraMap B C x) =
    Ideal.quotientMap I' (algebraMap B C) Ideal.le_comap_map (e.symm (algebraMap B B₀ x))
  have : e.symm (algebraMap B B₀ x) = Ideal.Quotient.mk I x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hπ x).symm
  rw [this, Ideal.quotientMap_mk]

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem pushPt_nsmulPt (L : RelativeGroupLaw R f) (u : A ⟶ A) (hu : u ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (P : SchemeHomOver t f) :
    pushPt u hu (nsmulPt L t m P) = nsmulPt L t m (pushPt u hu P) := by
  induction m with
  | zero =>
      change pushPt u hu (L.one t) = L.one t
      apply RelativeGroupLaw.eq_one_of_mul_self
      have := hhom t (L.one t) (L.one t)
      rw [L.one_mul] at this
      exact this.symm
  | succ m ih =>
      change pushPt u hu (L.mul t (nsmulPt L t m P) P) = L.mul t (nsmulPt L t m (pushPt u hu P)) (pushPt u hu P)
      rw [hhom, ih]

end reductionHelpers

section homHelpers
variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (e : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst e
  have h1 : x₁ = x₂ := Subtype.ext hx
  have h2 : y₁ = y₂ := Subtype.ext hy
  subst h1 h2
  rfl

theorem nsmulPt_mul (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (x y : SchemeHomOver t f) :
    nsmulPt L t m (L.mul t x y) = L.mul t (nsmulPt L t m x) (nsmulPt L t m y) := by
  induction m with
  | zero => change L.one t = L.mul t (L.one t) (L.one t); rw [L.one_mul]
  | succ m ih =>
      change L.mul t (nsmulPt L t m (L.mul t x y)) (L.mul t x y) =
        L.mul t (L.mul t (nsmulPt L t m x) x) (L.mul t (nsmulPt L t m y) y)
      rw [ih, L.mul_assoc, L.mul_assoc, ← L.mul_assoc t (nsmulPt L t m y) x y, hc t (nsmulPt L t m y) x,
        L.mul_assoc]

end homHelpers

end KB1Asm

open KB1Asm in
theorem solution
    {q : ℕ} [Fact q.Prime]

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (n : ℕ) (hn : ((q : ℕ) : B) ^ n = 0)

    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B)) (f' : A' ⟶ Spec (CommRingCat.of B))
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') (hc : L.IsCommutative) (hc' : L'.IsCommutative)
    (hA : AbelianSchemePropertyBundle B f) (hA' : AbelianSchemePropertyBundle B f')

    (F F' : MvFormalGroup 2 B)
    (θ : RelativeGroupLaw.FormalCoordinates f 2) (θ' : RelativeGroupLaw.FormalCoordinates f' 2)
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')

    {A₀ A₀' : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)) (f₀' : A₀' ⟶ Spec (CommRingCat.of B₀))
    (L₀ : RelativeGroupLaw B₀ f₀) (L₀' : RelativeGroupLaw B₀ f₀')
    (g : A₀ ⟶ A) (g' : A₀' ⟶ A')
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hg' : IsPullback g' f₀' f' (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg'mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀'),
      (L₀'.mul t P Q).1 ≫ g' =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1)

    (φ₀ : A₀ ⟶ A₀') (hφ₀ : φ₀ ≫ f₀' = f₀)
    (φ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      mapPt φ₀ hφ₀ (L₀.mul t P Q) = L₀'.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))

    (T : MvFormalGroup.Hom F F')
    (hTφ₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') f₀, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ φ₀ ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toPowerSeries i) s)).1) :
    ∃ (Ñ : A ⟶ A') (hÑ : Ñ ≫ f' = f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
        mapPt Ñ hÑ (L.mul t P Q) = L'.mul t (mapPt Ñ hÑ P) (mapPt Ñ hÑ Q)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t f₀),
        P.1 ≫ g ≫ Ñ = (nsmulPt L₀' t (q ^ (n * μ)) (mapPt φ₀ hφ₀ P)).1 ≫ g') ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (k : ℕ), J ^ (k + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ Ñ =
            (θ' B'' (fun i => MvFormalGroup.nilEval k
              (MvPowerSeries.subst T.toPowerSeries (F'.nthSeries (q ^ (n * μ)) i)) s)).1) := by
  classical
  have hgpb := hg
  have hg_mul := @hgmul
  have hg'pb := hg'
  have hg'_mul := @hg'mul
  haveI hsm : Smooth f' := hA'.smooth

  have hN : ((q ^ n : ℕ) : B) = 0 := by rw [Nat.cast_pow]; exact hn

  have hψ' : (φ₀ ≫ g') ≫ f' = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := by
    rw [Category.assoc, hg'pb.w, ← Category.assoc, hφ₀]
  obtain ⟨Ñf, hover, hnat, hchar⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
      hπ μ hμ (q ^ n) hN L' hc' F' θ' hθ' f f₀ g hgpb (φ₀ ≫ g') hψ'
  obtain ⟨Ñ, hÑf, hÑpt, -⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural f f' Ñf hover hnat

  have hIC : ∀ (C : Type) [CommRing C] [Algebra B C] (C' : Type) [CommRing C'] [Algebra C C'] [Algebra B C']
      [IsScalarTower B C C'],
      ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)).map (algebraMap C C') =
        (RingHom.ker (algebraMap B B₀)).map (algebraMap B C') := by
    intro C _ _ C' _ _ _ _
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

  have hInil : ∀ (C : Type) [CommRing C] [Algebra B C],
      IsNilpotent ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)) := by
    intro C _ _
    exact ⟨μ + 1, by rw [← Ideal.map_pow, hμ]; simp⟩

  have red : ∀ (C : Type) [CommRing C] [Algebra B C]
      [Algebra B₀ (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))]
      [IsScalarTower B B₀ (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))]
      (P : Spec (CommRingCat.of C) ⟶ A)
      (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B C))),
      ∃ P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))) ⟶ A₀,
        P₀ ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P ∧
        P₀ ≫ f₀ = Scheme.specOver (𝒪 := B₀) (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)) ∧
        (P₀ ≫ φ₀ ≫ g') ≫ f' = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
    intro C _ _ _ _ P hP
    have hcomm : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P) ≫ f =
        Scheme.specOver (𝒪 := B₀) (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := by
      rw [Category.assoc, hP, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    refine ⟨hgpb.lift _ _ hcomm, hgpb.lift_fst _ _ hcomm, hgpb.lift_snd _ _ hcomm, ?_⟩
    rw [Category.assoc, hψ', ← Category.assoc, hgpb.lift_snd _ _ hcomm]
    change Spec.map (CommRingCat.ofHom (algebraMap B₀ _)) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]

  have pieceChar : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ A)
      (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B C)))
      (P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))) ⟶ A₀)
      (hP₀ : P₀ ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P)
      (a : C) (x : Spec (CommRingCat.of (Localization.Away a)) ⟶ A')
      (hx : x ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a))))
      (hxl : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)).map (algebraMap C (Localization.Away a))))) ≫ x =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap
          (((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)).map (algebraMap C (Localization.Away a)))
          (algebraMap C (Localization.Away a)) Ideal.le_comap_map)) ≫ P₀ ≫ φ₀ ≫ g'),
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ Ñf C P hP =
        (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ((q ^ n) ^ μ) ⟨x, hx⟩).1 := by
    intro C _ _ P hP P₀ hP₀ a x hx hxl

    let Ca := Localization.Away a
    let loc : C →+* Ca := algebraMap C Ca
    let IC : Ideal C := (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)
    let ICa : Ideal Ca := (RingHom.ker (algebraMap B B₀)).map (algebraMap B Ca)
    have hIeq : IC.map loc = ICa := hIC C Ca

    have hPa : (Spec.map (CommRingCat.ofHom loc) ≫ P) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Ca)) := by
      rw [Category.assoc, hP, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hn : Ñf Ca (Spec.map (CommRingCat.ofHom loc) ≫ P) hPa = Spec.map (CommRingCat.ofHom loc) ≫ Ñf C P hP :=
      hnat C Ca (IsScalarTower.toAlgHom B C Ca) P hP hPa
    change Spec.map (CommRingCat.ofHom loc) ≫ Ñf C P hP = _
    rw [← hn]

    let ρ : C ⧸ IC →+* Ca ⧸ ICa := Ideal.quotientMap ICa loc (by rw [← hIeq]; exact Ideal.le_comap_map)
    let σ : Ca ⧸ IC.map loc →+* Ca ⧸ ICa := Ideal.quotientMap ICa (RingHom.id Ca) (by rw [hIeq]; exact le_of_eq (Ideal.comap_id _).symm)
    have hσ : (Ideal.Quotient.mk ICa) = σ.comp (Ideal.Quotient.mk (IC.map loc)) := by
      ext c; rfl
    have hρ : ρ = σ.comp (Ideal.quotientMap (IC.map loc) loc Ideal.le_comap_map) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

    refine hchar Ca (Spec.map (CommRingCat.ofHom loc) ≫ P) hPa (Spec.map (CommRingCat.ofHom ρ) ≫ P₀) ?_ x hx ?_
    · rw [Category.assoc, hP₀, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    · rw [hσ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hxl, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← hρ]
      exact rfl
  refine ⟨Ñ, hÑf, ?_, ?_, ?_⟩
  ·
    have X4b_affine : ∀ (C : Type) [CommRing C] [Algebra B C]
        (P Q : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f),
        mapPt Ñ hÑf (L.mul _ P Q) = L'.mul _ (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q) := by
      intro C _ _ P Q
      obtain ⟨instq, hst⟩ := exists_algebra_quotient_isScalarTower hπ C
      letI := instq; haveI := hst
      have hP : P.1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B C)) := P.2
      have hQ : Q.1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B C)) := Q.2
      have hPQ : (L.mul _ P Q).1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B C)) := (L.mul _ P Q).2
      obtain ⟨P₀, hP₀, hP₀f, hxP⟩ := red C P.1 hP
      obtain ⟨Q₀, hQ₀, hQ₀f, hxQ⟩ := red C Q.1 hQ
      let Cq := C ⧸ ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C))
      let t₀ : Spec (CommRingCat.of Cq) ⟶ Spec (CommRingCat.of B₀) := Scheme.specOver (𝒪 := B₀) Cq
      let p₀ : SchemeHomOver t₀ f₀ := ⟨P₀, hP₀f⟩
      let q₀ : SchemeHomOver t₀ f₀ := ⟨Q₀, hQ₀f⟩
      have ht₀ : t₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
        change Spec.map (CommRingCat.ofHom (algebraMap B₀ Cq)) ≫ _ = _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq]

      let z₀ : Spec (CommRingCat.of Cq) ⟶ pullback f' f' := pullback.lift (P₀ ≫ φ₀ ≫ g') (Q₀ ≫ φ₀ ≫ g') (hxP.trans hxQ.symm)
      have hz₀ : z₀ ≫ (pullback.fst f' f' ≫ f') =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
        rw [← Category.assoc, pullback.lift_fst]; exact hxP
      obtain ⟨ι, a, hspan, hlifts⟩ :=
        AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
          (pullback.fst f' f' ≫ f') ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)) (hInil C)
          (Spec.map (CommRingCat.ofHom (algebraMap B C))) z₀ hz₀
      apply Subtype.ext
      refine (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) a hspan).openCover.hom_ext _ _
        fun i => ?_
      change Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫ (L.mul _ P Q).1 ≫ Ñ =
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫
          (L'.mul _ (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q)).1

      let Ci := Localization.Away (a i)
      let loc : C →+* Ci := algebraMap C Ci
      let mki := Ideal.Quotient.mk (((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)).map loc)
      let qmi := Ideal.quotientMap (((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)).map loc) loc Ideal.le_comap_map
      obtain ⟨zi, hzi₀, hzil⟩ := hlifts i
      have hloc : Spec.map (CommRingCat.ofHom loc) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
          Spec.map (CommRingCat.ofHom (algebraMap B Ci)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
      have hxi : (zi ≫ pullback.fst f' f') ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B Ci)) := by
        rw [Category.assoc, hzi₀]; exact hloc
      have hyi : (zi ≫ pullback.snd f' f') ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B Ci)) := by
        rw [Category.assoc, ← pullback.condition, hzi₀]; exact hloc
      have hxil : Spec.map (CommRingCat.ofHom mki) ≫ (zi ≫ pullback.fst f' f') =
          Spec.map (CommRingCat.ofHom qmi) ≫ P₀ ≫ φ₀ ≫ g' := by
        rw [← Category.assoc, hzil, Category.assoc, pullback.lift_fst]
      have hyil : Spec.map (CommRingCat.ofHom mki) ≫ (zi ≫ pullback.snd f' f') =
          Spec.map (CommRingCat.ofHom qmi) ≫ Q₀ ≫ φ₀ ≫ g' := by
        rw [← Category.assoc, hzil, Category.assoc, pullback.lift_snd]
      let xi : SchemeHomOver (Scheme.specOver (𝒪 := B) Ci) f' := ⟨zi ≫ pullback.fst f' f', hxi⟩
      let yi : SchemeHomOver (Scheme.specOver (𝒪 := B) Ci) f' := ⟨zi ≫ pullback.snd f' f', hyi⟩
      have h1 := pieceChar C P.1 hP P₀ hP₀ (a i) xi.1 hxi hxil
      have h2 := pieceChar C Q.1 hQ Q₀ hQ₀ (a i) yi.1 hyi hyil

      have hPQ₀ : (L₀.mul t₀ p₀ q₀).1 ≫ g =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ (L.mul _ P Q).1 := by
        rw [hg_mul]
        have hn := congrArg Subtype.val (L.mul_natural (Scheme.specOver (𝒪 := B) C)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ Scheme.specOver (𝒪 := B) C)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C))))) rfl P Q)
        rw [schemeHomOverComp_coe] at hn
        rw [hn]
        exact mul_val_congr L ht₀ _ _ _ _ (by rw [schemeHomOverComp_coe]; exact hP₀)
          (by rw [schemeHomOverComp_coe]; exact hQ₀)

      let w : SchemeHomOver (Scheme.specOver (𝒪 := B) Ci) f' := L'.mul _ xi yi
      have hwl : Spec.map (CommRingCat.ofHom mki) ≫ w.1 =
          Spec.map (CommRingCat.ofHom qmi) ≫ (L₀.mul t₀ p₀ q₀).1 ≫ φ₀ ≫ g' := by

        have hl := congrArg Subtype.val (L'.mul_natural (Scheme.specOver (𝒪 := B) Ci)
          (Spec.map (CommRingCat.ofHom mki) ≫ Scheme.specOver (𝒪 := B) Ci) (Spec.map (CommRingCat.ofHom mki)) rfl xi yi)
        rw [schemeHomOverComp_coe] at hl
        rw [hl]

        have hr1 := congrArg Subtype.val (φ₀_mul t₀ p₀ q₀)
        rw [mapPt_coe] at hr1
        rw [← Category.assoc ((L₀.mul t₀ p₀ q₀).1), hr1, hg'_mul]
        have hr2 := congrArg Subtype.val (L'.mul_natural (t₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          (Spec.map (CommRingCat.ofHom qmi) ≫ t₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          (Spec.map (CommRingCat.ofHom qmi)) rfl
          ⟨(mapPt φ₀ hφ₀ p₀).1 ≫ g', by rw [Category.assoc, hg'pb.w, ← Category.assoc, (mapPt φ₀ hφ₀ p₀).2]⟩
          ⟨(mapPt φ₀ hφ₀ q₀).1 ≫ g', by rw [Category.assoc, hg'pb.w, ← Category.assoc, (mapPt φ₀ hφ₀ q₀).2]⟩)
        rw [schemeHomOverComp_coe] at hr2
        rw [hr2]
        refine mul_val_congr L' ?_ _ _ _ _ ?_ ?_
        · rw [ht₀]
          change Spec.map (CommRingCat.ofHom mki) ≫ Spec.map (CommRingCat.ofHom (algebraMap B Ci)) =
            Spec.map (CommRingCat.ofHom qmi) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap B C))
          simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl
        · rw [schemeHomOverComp_coe, schemeHomOverComp_coe]; exact hxil
        · rw [schemeHomOverComp_coe, schemeHomOverComp_coe]; exact hyil
      have h3 := pieceChar C (L.mul _ P Q).1 hPQ (L₀.mul t₀ p₀ q₀).1 hPQ₀ (a i) w.1 w.2 hwl

      rw [hÑpt C _ hPQ, h3]
      have hr := congrArg Subtype.val (L'.mul_natural (Scheme.specOver (𝒪 := B) C)
        (Spec.map (CommRingCat.ofHom loc) ≫ Scheme.specOver (𝒪 := B) C) (Spec.map (CommRingCat.ofHom loc)) rfl
        (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q))
      rw [schemeHomOverComp_coe] at hr
      change _ = Spec.map (CommRingCat.ofHom loc) ≫ (L'.mul _ (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q)).1
      rw [hr, Subtype.coe_eta, ← nsmulPt_eq_nsmul, nsmulPt_mul L' hc']
      refine mul_val_congr L' hloc.symm _ _ _ _ ?_ ?_
      · rw [schemeHomOverComp_coe, mapPt_coe, hÑpt C _ hP, h1, nsmulPt_eq_nsmul]
      · rw [schemeHomOverComp_coe, mapPt_coe, hÑpt C _ hQ, h2, nsmulPt_eq_nsmul]
    intro T t P Q
    exact mapPt_mul_of_affine L L' Ñ hÑf X4b_affine t P Q
  ·
    have key : ∀ (S : CommRingCat.{0}) (t' : Spec S ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' f₀),
        P.1 ≫ g ≫ Ñ = (nsmulPt L₀' t' (q ^ (n * μ)) (mapPt φ₀ hφ₀ P)).1 ≫ g' := by
      intro S t' P
      obtain ⟨inst₀, ht'⟩ := exists_algebra_eq_specOver (R := B₀) S t'
      subst ht'
      letI instB : Algebra B S := ((algebraMap B₀ S).comp (algebraMap B B₀)).toAlgebra
      have halg : Spec.map (CommRingCat.ofHom (algebraMap B₀ S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) =
          Spec.map (CommRingCat.ofHom (algebraMap B S)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hP : (P.1 ≫ g) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B S)) := by
        rw [Category.assoc, hgpb.w, ← Category.assoc, P.2]; exact halg
      let J : Ideal S := (RingHom.ker (algebraMap B B₀)).map (algebraMap B S)
      have hx : (P.1 ≫ φ₀ ≫ g') ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B S)) := by
        rw [Category.assoc, Category.assoc, hg'pb.w, ← Category.assoc φ₀, hφ₀, ← Category.assoc, P.2]; exact halg
      have hc := hchar S (P.1 ≫ g) hP (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1)
        (by rw [Category.assoc]) (P.1 ≫ φ₀ ≫ g') hx (by rw [Category.assoc])
      rw [← Category.assoc, hÑpt S (P.1 ≫ g) hP, hc, ← nsmulPt_eq_nsmul, ← pow_mul,
        nsmulPt_comp_of_mul_comp (algebraMap B B₀) L' L₀' g' hg'pb.w hg'_mul]
      exact nsmulPt_val_congr L' halg.symm _ _ _ (by simp only [mapPt_coe, Category.assoc])

    intro T t P
    refine T.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
    change T.affineOpenCover.f i ≫ P.1 ≫ g ≫ Ñ =
      T.affineOpenCover.f i ≫ (nsmulPt L₀' t (q ^ (n * μ)) (mapPt φ₀ hφ₀ P)).1 ≫ g'
    have h1 := key (T.affineOpenCover.X i) (T.affineOpenCover.f i ≫ t)
      (schemeHomOverComp (T.affineOpenCover.f i) rfl P)
    rw [schemeHomOverComp_coe, Category.assoc] at h1
    rw [h1, ← Category.assoc (T.affineOpenCover.f i), ← schemeHomOverComp_coe (T.affineOpenCover.f i) rfl,
      nsmulPt_natural, mapPt_schemeHomOverComp]
  ·
    intro B'' _ _ J k hJ s hs
    obtain ⟨hθnat, -⟩ := id hθ
    obtain ⟨hθ'nat, hθ'J⟩ := id hθ'
    have hT0 : ∀ i, MvPowerSeries.constantCoeff (T.toPowerSeries i) = 0 := T.constantCoeff_eq_zero

    let u : Fin 2 → B'' := fun i => MvFormalGroup.nilEval k (T.toPowerSeries i) s
    have hu : ∀ i, u i ∈ J := (MvFormalGroup.nilEval_subst_of_mem J k hJ s hs T.toPowerSeries hT0 0).1
    have hsnil : ∀ i, IsNilpotent (s i) := fun i =>
      ⟨k + 1, by have h := Ideal.pow_mem_pow (hs i) (k + 1); rw [hJ] at h; exact (Submodule.mem_bot B'').mp h⟩
    have hunil : ∀ i, IsNilpotent (u i) := fun i =>
      ⟨k + 1, by have h := Ideal.pow_mem_pow (hu i) (k + 1); rw [hJ] at h; exact (Submodule.mem_bot B'').mp h⟩

    let I : Ideal B := RingHom.ker (algebraMap B B₀)
    let I' : Ideal B'' := I.map (algebraMap B B'')
    let e : (B ⧸ I) ≃+* B₀ := RingHom.quotientKerEquivOfSurjective hπ
    let χ : B₀ →+* B'' ⧸ I' := (Ideal.quotientMap I' (algebraMap B B'') Ideal.le_comap_map).comp e.symm.toRingHom
    letI instq : Algebra B₀ (B'' ⧸ I') := χ.toAlgebra
    haveI : IsScalarTower B B₀ (B'' ⧸ I') := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      change Ideal.Quotient.mk I' (algebraMap B B'' x) =
        Ideal.quotientMap I' (algebraMap B B'') Ideal.le_comap_map (e.symm (algebraMap B B₀ x))
      have : e.symm (algebraMap B B₀ x) = Ideal.Quotient.mk I x := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (RingHom.quotientKerEquivOfSurjective_apply_mk hπ x).symm
      rw [this, Ideal.quotientMap_mk]
    let πq : B'' →ₐ[B] B'' ⧸ I' := Ideal.Quotient.mkₐ B I'
    have hπq : πq.toRingHom = Ideal.Quotient.mk I' := rfl

    let sq : Fin 2 → B'' ⧸ I' := πq ∘ s
    let Jq : Ideal (B'' ⧸ I') := J.map (Ideal.Quotient.mk I')
    have hJq : Jq ^ (k + 1) = ⊥ := by
      change (J.map (Ideal.Quotient.mk I')) ^ (k + 1) = ⊥
      rw [← Ideal.map_pow, hJ]; simp
    have hsq : ∀ i, sq i ∈ Jq := fun i => Ideal.mem_map_of_mem _ (hs i)

    have hθq1 : (θ (B'' ⧸ I') sq).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I')) ≫ (θ B'' s).1 := by
      have h := congrArg Subtype.val (hθnat B'' (B'' ⧸ I') πq s hsnil)
      rwa [schemeHomOverComp_coe, hπq] at h

    have hcomm : (θ (B'' ⧸ I') sq).1 ≫ f =
        Scheme.specOver (𝒪 := B₀) (B'' ⧸ I') ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := by
      rw [(θ (B'' ⧸ I') sq).2]
      change Spec.map (CommRingCat.ofHom (algebraMap B (B'' ⧸ I'))) =
        Spec.map (CommRingCat.ofHom (algebraMap B₀ (B'' ⧸ I'))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    let P₀ : Spec (CommRingCat.of (B'' ⧸ I')) ⟶ A₀ := hgpb.lift _ _ hcomm
    have hP₀g : P₀ ≫ g = (θ (B'' ⧸ I') sq).1 := hgpb.lift_fst _ _ hcomm
    have hP₀f : P₀ ≫ f₀ = Scheme.specOver (𝒪 := B₀) (B'' ⧸ I') := hgpb.lift_snd _ _ hcomm

    have hT := hTφ₀ (B'' ⧸ I') Jq k hJq sq hsq ⟨P₀, hP₀f⟩ hP₀g

    have hlift : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I')) ≫ (θ' B'' u).1 = P₀ ≫ φ₀ ≫ g' := by
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I')) ≫ (θ' B'' u).1 =
        (⟨P₀, hP₀f⟩ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) (B'' ⧸ I')) f₀).1 ≫ φ₀ ≫ g'
      rw [hT]
      have h := congrArg Subtype.val (hθ'nat B'' (B'' ⧸ I') πq u hunil)
      rw [schemeHomOverComp_coe, hπq] at h
      have hu' : (πq ∘ u) = fun i => MvFormalGroup.nilEval k (T.toPowerSeries i) sq :=
        funext fun i => map_nilEval πq k (T.toPowerSeries i) s
      rw [← h, hu']

    have hP := (θ B'' s).2
    have hc := hchar B'' (θ B'' s).1 hP P₀ (by rw [hP₀g, hθq1]) (θ' B'' u).1 (θ' B'' u).2 hlift
    rw [hÑpt B'' _ hP, hc, Subtype.coe_eta, ← nsmulPt_eq_nsmul, ← pow_mul, nsmulPt_eq_nsmul]
    change (L'.nsmul (Scheme.specOver (𝒪 := B) B'') (q ^ (n * μ)) (θ' B'' u)).1 = _
    rw [nsmul_formalCoordinates_eq_iterate L' F' θ' hθ' J k hJ u hu]

    congr 2
    funext i
    rw [(MvFormalGroup.nilEval_subst_of_mem J k hJ s hs T.toPowerSeries hT0 _).2]
    exact ((nilEval_nthSeries_of_mem F' J k hJ u hu (q ^ (n * μ))).2 i).symm

end S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_lift_nsmul_pow_of_isFormalCoordinates
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_lift_nsmul_pow_of_isFormalCoordinates (solution)
