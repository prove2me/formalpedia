-- Prove2me | solution 1 for Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ba1a2da1-6c28-5186-975d-9291b97bc8fd

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit
import Theorems.Thm_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
import Theorems.Thm_Module_Grassmannian_adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq
import Theorems.Thm_Module_Grassmannian_exists_injective_and_bijective_of_span_eq_top
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents

open scoped TensorProduct
open TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GrassPluckerEmb

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)

structure Rep where
  Gr : Scheme.{0}
  p : Gr ⟶ Spec (CommRingCat.of R)
  pt : ∀ (A : Type) [CommRing A] [Algebra R A],
    Module.Grassmannian A (A ⊗[R] M) k ≃
      {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}
  hpt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
    (N : Module.Grassmannian A (A ⊗[R] M) k),
    (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1
  V : (Fin k → M) → Gr.Opens
  hV : ⨆ x, V x = ⊤
  hVaff : ∀ x, IsAffineOpen (V x)
  hVchart : ∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A]
    (N : Module.Grassmannian A (A ⊗[R] M) k),
    Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
      Function.Bijective fun v : Fin k → A =>
        ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)

variable {R M k}

def InChart (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A]
    (N : Module.Grassmannian A (A ⊗[R] M) k) : Prop :=
  Function.Bijective fun v : Fin k → A => ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)

section points

variable (D : Rep R M k)

@[reducible] noncomputable def algOfHom {A : Type} [CommRing A] (h : Spec (CommRingCat.of A) ⟶ D.Gr) : Algebra R A :=
  (Spec.preimage (h ≫ D.p)).hom.toAlgebra

theorem specMap_algebraMap_algOfHom {A : Type} [CommRing A] (h : Spec (CommRingCat.of A) ⟶ D.Gr) :
    letI := algOfHom D h
    Spec.map (CommRingCat.ofHom (algebraMap R A)) = h ≫ D.p := by
  letI := algOfHom D h
  change Spec.map (CommRingCat.ofHom (Spec.preimage (h ≫ D.p)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

noncomputable def ptOf {A : Type} [CommRing A] (h : Spec (CommRingCat.of A) ⟶ D.Gr) :
    letI := algOfHom D h
    Module.Grassmannian A (A ⊗[R] M) k :=
  letI := algOfHom D h
  (D.pt A).symm ⟨h, (specMap_algebraMap_algOfHom D h).symm⟩

theorem pt_ptOf {A : Type} [CommRing A] (h : Spec (CommRingCat.of A) ⟶ D.Gr) :
    letI := algOfHom D h
    (D.pt A (ptOf D h)).1 = h := by
  letI := algOfHom D h
  change (D.pt A ((D.pt A).symm ⟨h, _⟩)).1 = h
  rw [Equiv.apply_symm_apply]

theorem exists_algHom {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ ρ : A →ₐ[R] B, Spec.map (CommRingCat.ofHom ρ.toRingHom) = s := by
  let ρ₀ : A →+* B := (Spec.preimage s).hom
  have hρ₀ : Spec.map (CommRingCat.ofHom ρ₀) = s := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomp : ρ₀.comp (algebraMap R A) = algebraMap R B := by
    have h1 : Spec.map (CommRingCat.ofHom (ρ₀.comp (algebraMap R A))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hρ₀, hs]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨⟨ρ₀, fun r => ?_⟩, hρ₀⟩
  exact RingHom.congr_fun hcomp r

theorem map_eq_of_pt {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ρ : A →ₐ[R] B) (NA : Module.Grassmannian A (A ⊗[R] M) k) (NB : Module.Grassmannian B (B ⊗[R] M) k)
    (h : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ (D.pt A NA).1 = (D.pt B NB).1) :
    Module.Grassmannian.map ρ NA = NB := by
  apply (D.pt B).injective
  apply Subtype.ext
  rw [D.hpt A B ρ NA, h]

end points

section charts

variable (D : Rep R M k)

def S (x : Fin k → M) : Type := Γ(D.Gr, D.V x)

noncomputable scoped instance (x : Fin k → M) : CommRing (S D x) := inferInstanceAs (CommRing Γ(D.Gr, D.V x))

noncomputable def gS (x : Fin k → M) : Spec (CommRingCat.of (S D x)) ⟶ D.Gr := (D.hVaff x).fromSpec

scoped instance (x : Fin k → M) : IsOpenImmersion (gS D x) :=
  inferInstanceAs (IsOpenImmersion (D.hVaff x).fromSpec)

theorem opensRange_gS (x : Fin k → M) : (gS D x).opensRange = D.V x := (D.hVaff x).opensRange_fromSpec

theorem range_gS (x : Fin k → M) : Set.range (gS D x).base = (D.V x : Set D.Gr) := (D.hVaff x).range_fromSpec

noncomputable scoped instance algS (x : Fin k → M) : Algebra R (S D x) := algOfHom D (gS D x)

theorem specMap_algebraMap_S (x : Fin k → M) :
    Spec.map (CommRingCat.ofHom (algebraMap R (S D x))) = gS D x ≫ D.p :=
  specMap_algebraMap_algOfHom D (gS D x)

noncomputable def NS (x : Fin k → M) : Module.Grassmannian (S D x) (S D x ⊗[R] M) k := ptOf D (gS D x)

theorem pt_NS (x : Fin k → M) : (D.pt (S D x) (NS D x)).1 = gS D x := pt_ptOf D (gS D x)

theorem NS_inChart (x : Fin k → M) : InChart x (NS D x) := by
  refine (D.hVchart x (S D x) (NS D x)).mp ?_
  rw [pt_NS, range_gS]

end charts

section plucker

variable (R M k)

theorem exists_Pl :
    ∃ P : ∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M),
        {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N} → (Fin k → M) → A,
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (m : M),
          ∑ i, P A x N (Function.update x i m) • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (y : Fin k → M),
          P A x N y = (Matrix.of fun i j => P A x N (Function.update x i (y j))).det) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}), P A x N x = 1) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (x : Fin k → M) (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}),
          ∃ h : InChart x (Module.Grassmannian.map φ N.1),
            ∀ y : Fin k → M, P B x ⟨Module.Grassmannian.map φ N.1, h⟩ y = φ (P A x N y)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (y : Fin k → M),
          InChart y N.1 ↔ IsUnit (P A x N y)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (y : Fin k → M)
          (hy : InChart y N.1) (z : Fin k → M),
          P A x N z = P A x N y * P A y ⟨N.1, hy⟩ z) :=
  Module.Grassmannian.exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit R M k

noncomputable def Pl {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (y : Fin k → M) : A :=
  (exists_Pl R M k).choose A x N y

theorem Pl_expand {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (m : M) :
    ∑ i, Pl R M k x N (Function.update x i m) • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
      N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m) :=
  (exists_Pl R M k).choose_spec.1 A x N m

theorem Pl_self {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) : Pl R M k x N x = 1 :=
  (exists_Pl R M k).choose_spec.2.2.1 A x N

theorem Pl_natural {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
    (x : Fin k → M) (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) :
    ∃ h : InChart x (Module.Grassmannian.map φ N.1),
      ∀ y : Fin k → M, Pl R M k x ⟨Module.Grassmannian.map φ N.1, h⟩ y = φ (Pl R M k x N y) :=
  (exists_Pl R M k).choose_spec.2.2.2.1 A B φ x N

theorem inChart_iff_isUnit {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (y : Fin k → M) :
    InChart y N.1 ↔ IsUnit (Pl R M k x N y) :=
  (exists_Pl R M k).choose_spec.2.2.2.2.1 A x N y

theorem Pl_mul {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (y : Fin k → M)
    (hy : InChart y N.1) (z : Fin k → M) :
    Pl R M k x N z = Pl R M k x N y * Pl R M k y ⟨N.1, hy⟩ z :=
  (exists_Pl R M k).choose_spec.2.2.2.2.2 A x N y hy z

variable {R M k}

theorem Pl_congr {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N N' : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (h : N.1 = N'.1) (y : Fin k → M) :
    Pl R M k x N y = Pl R M k x N' y := by
  cases N; cases N'; cases h; rfl

theorem eq_Pl_update {A : Type} [CommRing A] [Algebra R A] (x : Fin k → M)
    (N : {N : Module.Grassmannian A (A ⊗[R] M) k // InChart x N}) (m : M) (c : Fin k → A)
    (hc : ∑ j, c j • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x j) = N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m))
    (i : Fin k) : c i = Pl R M k x N (Function.update x i m) := by
  have h := hc.trans (Pl_expand R M k x N m).symm
  exact congrFun (N.2.1 h) i

end plucker

section index

variable (n : ℕ) (k)

def mm : ℕ := (n + 1) ^ k - 1

theorem mm_succ : mm k n + 1 = (n + 1) ^ k :=
  Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.succ_pos n))

def ε : Fin (mm k n + 1) ≃ (Fin k → Fin (n + 1)) :=
  (finCongr (mm_succ k n)).trans finFunctionFinEquiv.symm

variable {k n}

def τ (g : Fin (n + 1) → M) (l : Fin (mm k n + 1)) : Fin k → M := g ∘ (ε k n l)

theorem τ_symm (g : Fin (n + 1) → M) (I : Fin k → Fin (n + 1)) : τ g ((ε k n).symm I) = g ∘ I := by
  unfold τ; rw [Equiv.apply_symm_apply]

theorem update_τ (g : Fin (n + 1) → M) (l : Fin (mm k n + 1)) (i : Fin k) (a : Fin (n + 1)) :
    Function.update (τ g l) i (g a) = τ g ((ε k n).symm (Function.update (ε k n l) i a)) := by
  rw [τ_symm]
  unfold τ
  rw [Function.comp_update]

end index

section chartmaps

variable (D : Rep R M k) {n : ℕ} (g : Fin (n + 1) → M)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (mm k n + 1)) R
local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule (Fin (mm k n + 1)) R)

noncomputable def Nτ (l : Fin (mm k n + 1)) :
    {N : Module.Grassmannian (S D (τ g l)) (S D (τ g l) ⊗[R] M) k // InChart (τ g l) N} :=
  ⟨NS D (τ g l), NS_inChart D (τ g l)⟩

noncomputable def a (l : Fin (mm k n + 1)) : Fin (mm k n + 1) → S D (τ g l) :=
  fun l' => Pl R M k (τ g l) (Nτ D g l) (τ g l')

theorem a_self (l : Fin (mm k n + 1)) : a D g l l = 1 := Pl_self R M k _ _

theorem exists_ψ (l : Fin (mm k n + 1)) :
    ∃ ψ : Away 𝒜 (MvPolynomial.X l : MvPolynomial (Fin (mm k n + 1)) R) →ₐ[R] S D (τ g l),
      ∀ l', ψ (ProjSpace.ratio R (mm k n) l l') = a D g l l' :=
  AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq R (mm k n) l (a D g l) (a_self D g l)

noncomputable def ψ (l : Fin (mm k n + 1)) :
    Away 𝒜 (MvPolynomial.X l : MvPolynomial (Fin (mm k n + 1)) R) →ₐ[R] S D (τ g l) :=
  (exists_ψ D g l).choose

theorem ψ_ratio (l l' : Fin (mm k n + 1)) : ψ D g l (ProjSpace.ratio R (mm k n) l l') = a D g l l' :=
  (exists_ψ D g l).choose_spec l'

noncomputable abbrev awayιX (l : Fin (mm k n + 1)) :
    Spec (CommRingCat.of (Away 𝒜 (MvPolynomial.X l : MvPolynomial (Fin (mm k n + 1)) R))) ⟶ ℙ :=
  Proj.awayι 𝒜 (MvPolynomial.X l) (ProjSpace.X_mem_one R (mm k n) l) one_pos

noncomputable def fS (l : Fin (mm k n + 1)) : Spec (CommRingCat.of (S D (τ g l))) ⟶ ℙ :=
  Spec.map (CommRingCat.ofHom (ψ D g l).toRingHom) ≫ awayιX (R := R) l

noncomputable def sV (x : Fin k → M) : (D.V x : Scheme.{0}) ⟶ Spec (CommRingCat.of (S D x)) :=
  (D.hVaff x).isoSpec.hom

scoped instance (x : Fin k → M) : IsIso (sV D x) := inferInstanceAs (IsIso (D.hVaff x).isoSpec.hom)

theorem sV_gS (x : Fin k → M) : sV D x ≫ gS D x = (D.V x).ι := by
  change (D.hVaff x).isoSpec.hom ≫ (D.hVaff x).fromSpec = _
  rw [← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

noncomputable def fV (l : Fin (mm k n + 1)) : (D.V (τ g l) : Scheme.{0}) ⟶ ℙ :=
  sV D (τ g l) ≫ fS D g l

end chartmaps

section residue

variable (D : Rep R M k)

abbrev κ (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) : Type := z.asIdeal.ResidueField

noncomputable def φκ (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) : S D x₀ →ₐ[R] κ D x₀ z :=
  IsScalarTower.toAlgHom R (S D x₀) (κ D x₀ z)

theorem φκ_apply (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) (s : S D x₀) :
    φκ D x₀ z s = algebraMap (S D x₀) (κ D x₀ z) s := rfl

noncomputable def Nκ (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) :
    Module.Grassmannian (κ D x₀ z) (κ D x₀ z ⊗[R] M) k :=
  Module.Grassmannian.map (φκ D x₀ z) (NS D x₀)

theorem pt_Nκ (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) :
    (D.pt (κ D x₀ z) (Nκ D x₀ z)).1 =
      Spec.map (CommRingCat.ofHom (algebraMap (S D x₀) (κ D x₀ z))) ≫ gS D x₀ := by
  unfold Nκ
  rw [D.hpt, pt_NS]
  rfl

theorem specMap_residue_apply (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) :
    Spec.map (CommRingCat.ofHom (algebraMap (S D x₀) (κ D x₀ z)))
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (κ D x₀ z)) = z := by
  rw [Spec.map_apply]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap (S D x₀) (κ D x₀ z)) ⊥ = z.asIdeal
  rw [← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem gS_mem_of_inChart (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) (x : Fin k → M)
    (h : InChart x (Nκ D x₀ z)) : (gS D x₀).base z ∈ D.V x := by
  have hsub := (D.hVchart x (κ D x₀ z) (Nκ D x₀ z)).mpr h
  rw [pt_Nκ] at hsub
  apply hsub
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (κ D x₀ z)), ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.comp_app]
  congr 1
  exact specMap_residue_apply D x₀ z

theorem inChart_of_notMem (x₀ : Fin k → M) (z : PrimeSpectrum (S D x₀)) (y : Fin k → M)
    (h : Pl R M k x₀ ⟨NS D x₀, NS_inChart D x₀⟩ y ∉ z.asIdeal) : InChart y (Nκ D x₀ z) := by
  obtain ⟨hc, hnat⟩ := Pl_natural R M k (φκ D x₀ z) x₀ ⟨NS D x₀, NS_inChart D x₀⟩
  have hu : IsUnit (Pl R M k x₀ ⟨Module.Grassmannian.map (φκ D x₀ z) (NS D x₀), hc⟩ y) := by
    rw [hnat y, φκ_apply,
      IsScalarTower.algebraMap_apply (S D x₀) (Localization.AtPrime z.asIdeal) (κ D x₀ z)]
    exact (IsLocalization.map_units (Localization.AtPrime z.asIdeal)
      (⟨_, show _ ∈ z.asIdeal.primeCompl from h⟩ : z.asIdeal.primeCompl)).map _
  change InChart y (Module.Grassmannian.map (φκ D x₀ z) (NS D x₀))
  exact (inChart_iff_isUnit R M k x₀ ⟨Module.Grassmannian.map (φκ D x₀ z) (NS D x₀), hc⟩ y).mpr hu

variable {n : ℕ} (g : Fin (n + 1) → M) (hg : Submodule.span R (Set.range g) = ⊤)

include hg in

theorem exists_mem_V_τ (y : D.Gr) : ∃ l : Fin (mm k n + 1), y ∈ D.V (τ g l) := by
  have hy : y ∈ (⨆ x, D.V x) := by rw [D.hV]; trivial
  obtain ⟨x₀, hx₀⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← SetLike.mem_coe, ← range_gS D x₀] at hx₀
  obtain ⟨z, rfl⟩ := hx₀
  obtain ⟨I, -, hI⟩ := Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top R M k (Fin (n + 1)) g hg
    (κ D x₀ z) (Nκ D x₀ z)
  refine ⟨(ε k n).symm I, ?_⟩
  apply gS_mem_of_inChart
  rw [τ_symm]
  exact hI

include hg in
theorem iSup_V_τ : ⨆ l : Fin (mm k n + 1), D.V (τ g l) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr (exists_mem_V_τ D g hg y)

end residue

section glue

variable (D : Rep R M k) {n : ℕ} (g : Fin (n + 1) → M) (hg : Submodule.span R (Set.range g) = ⊤)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (mm k n + 1)) R
local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule (Fin (mm k n + 1)) R)

theorem fS_indep {B : Type} [CommRing B] [Algebra R B] (NB : Module.Grassmannian B (B ⊗[R] M) k)
    (l₁ l₂ : Fin (mm k n + 1))
    (s₁ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (S D (τ g l₁))))
    (s₂ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (S D (τ g l₂))))
    (hs₁ : s₁ ≫ gS D (τ g l₁) = (D.pt B NB).1) (hs₂ : s₂ ≫ gS D (τ g l₂) = (D.pt B NB).1) :
    s₁ ≫ fS D g l₁ = s₂ ≫ fS D g l₂ := by

  have key : ∀ (l : Fin (mm k n + 1)) (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (S D (τ g l)))),
      s ≫ gS D (τ g l) = (D.pt B NB).1 →
      ∃ ρ : S D (τ g l) →ₐ[R] B, Spec.map (CommRingCat.ofHom ρ.toRingHom) = s ∧
        Module.Grassmannian.map ρ (NS D (τ g l)) = NB := by
    intro l s hs
    have hs' : s ≫ Spec.map (CommRingCat.ofHom (algebraMap R (S D (τ g l)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      rw [specMap_algebraMap_S, ← Category.assoc, hs]
      exact (D.pt B NB).2
    obtain ⟨ρ, hρ⟩ := exists_algHom s hs'
    refine ⟨ρ, hρ, map_eq_of_pt D ρ _ _ ?_⟩
    rw [hρ, pt_NS, hs]
  obtain ⟨ρ₁, hρ₁, hN₁⟩ := key l₁ s₁ hs₁
  obtain ⟨ρ₂, hρ₂, hN₂⟩ := key l₂ s₂ hs₂
  obtain ⟨h₁, hnat₁⟩ := Pl_natural R M k ρ₁ (τ g l₁) (Nτ D g l₁)
  obtain ⟨h₂, hnat₂⟩ := Pl_natural R M k ρ₂ (τ g l₂) (Nτ D g l₂)

  set N₁ : {N : Module.Grassmannian B (B ⊗[R] M) k // InChart (τ g l₁) N} :=
    ⟨Module.Grassmannian.map ρ₁ (Nτ D g l₁).1, h₁⟩ with hN₁def
  set N₂ : {N : Module.Grassmannian B (B ⊗[R] M) k // InChart (τ g l₂) N} :=
    ⟨Module.Grassmannian.map ρ₂ (Nτ D g l₂).1, h₂⟩ with hN₂def
  have e₁ : N₁.1 = NB := hN₁
  have e₂ : N₂.1 = NB := hN₂
  have hy : InChart (τ g l₂) N₁.1 := by rw [e₁, ← e₂]; exact N₂.2

  have hi : IsUnit (Pl R M k (τ g l₁) N₁ (τ g l₁)) := by rw [Pl_self]; exact isUnit_one
  have hj : IsUnit (Pl R M k (τ g l₁) N₁ (τ g l₂)) := (inChart_iff_isUnit R M k (τ g l₁) N₁ (τ g l₂)).mp hy
  have hψ₁ : ∀ l', (ρ₁.comp (ψ D g l₁)) (ProjSpace.ratio R (mm k n) l₁ l') * Pl R M k (τ g l₁) N₁ (τ g l₁) =
      Pl R M k (τ g l₁) N₁ (τ g l') := fun l' => by
    rw [Pl_self, mul_one, AlgHom.comp_apply, ψ_ratio]
    exact (hnat₁ (τ g l')).symm
  have hψ₂ : ∀ l', (ρ₂.comp (ψ D g l₂)) (ProjSpace.ratio R (mm k n) l₂ l') * Pl R M k (τ g l₁) N₁ (τ g l₂) =
      Pl R M k (τ g l₁) N₁ (τ g l') := fun l' => by
    rw [AlgHom.comp_apply, ψ_ratio]
    change ρ₂ (Pl R M k (τ g l₂) (Nτ D g l₂) (τ g l')) * _ = _
    rw [← hnat₂ (τ g l'), Pl_mul R M k (τ g l₁) N₁ (τ g l₂) hy (τ g l'), mul_comm,
      Pl_congr (τ g l₂) N₂ ⟨N₁.1, hy⟩ (e₂.trans e₁.symm)]
  have hcmp := AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq R (mm k n) B
    (fun l' => Pl R M k (τ g l₁) N₁ (τ g l')) l₁ l₂ hi hj (ρ₁.comp (ψ D g l₁)) (ρ₂.comp (ψ D g l₂)) hψ₁ hψ₂

  unfold fS
  rw [← hρ₁, ← hρ₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact hcmp

noncomputable def 𝒰 : D.Gr.OpenCover :=
  D.Gr.openCoverOfIsOpenCover (fun l : Fin (mm k n + 1) => D.V (τ g l)) (.mk (iSup_V_τ D g hg))

theorem 𝒰_f (l : Fin (mm k n + 1)) : (𝒰 D g hg).f l = (D.V (τ g l)).ι := rfl

theorem fV_compat (l₁ l₂ : Fin (mm k n + 1)) :
    pullback.fst ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂) ≫ fV D g l₁ =
      pullback.snd ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂) ≫ fV D g l₂ := by
  set Pb := pullback ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂)
  refine Scheme.Cover.hom_ext (Pb.affineOpenCover.openCover) _ _ fun i => ?_
  let B : Type := Pb.affineOpenCover.X i
  let w : Spec (CommRingCat.of B) ⟶ Pb := Pb.affineOpenCover.f i
  let t₁ : Spec (CommRingCat.of B) ⟶ (D.V (τ g l₁) : Scheme.{0}) :=
    w ≫ pullback.fst ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂)
  let t₂ : Spec (CommRingCat.of B) ⟶ (D.V (τ g l₂) : Scheme.{0}) :=
    w ≫ pullback.snd ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂)
  let h : Spec (CommRingCat.of B) ⟶ D.Gr := t₁ ≫ (D.V (τ g l₁)).ι
  letI : Algebra R B := algOfHom D h
  let NB : Module.Grassmannian B (B ⊗[R] M) k := ptOf D h
  have hNB : (D.pt B NB).1 = h := pt_ptOf D h
  have h₂ : t₂ ≫ (D.V (τ g l₂)).ι = h := by
    change (w ≫ pullback.snd ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂)) ≫ (𝒰 D g hg).f l₂ =
      (w ≫ pullback.fst ((𝒰 D g hg).f l₁) ((𝒰 D g hg).f l₂)) ≫ (𝒰 D g hg).f l₁
    rw [Category.assoc, Category.assoc, pullback.condition]
  have e := fS_indep D g NB l₁ l₂ (t₁ ≫ sV D (τ g l₁)) (t₂ ≫ sV D (τ g l₂))
    (by rw [hNB, Category.assoc, sV_gS]) (by rw [hNB, Category.assoc, sV_gS, h₂])
  rw [← Category.assoc, ← Category.assoc]
  change t₁ ≫ (sV D (τ g l₁) ≫ fS D g l₁) = t₂ ≫ (sV D (τ g l₂) ≫ fS D g l₂)
  rw [← Category.assoc, ← Category.assoc]
  exact e

noncomputable def ιmap : D.Gr ⟶ ℙ :=
  (𝒰 D g hg).glueMorphisms (fun l => fV D g l) (fV_compat D g hg)

theorem Vι_ιmap (l : Fin (mm k n + 1)) : (D.V (τ g l)).ι ≫ ιmap D g hg = fV D g l :=
  (𝒰 D g hg).ι_glueMorphisms (fun l => fV D g l) (fV_compat D g hg) l

theorem gS_ιmap (l : Fin (mm k n + 1)) : gS D (τ g l) ≫ ιmap D g hg = fS D g l := by
  have h := Vι_ιmap D g hg l
  unfold fV at h
  rw [← sV_gS, Category.assoc] at h
  exact (cancel_epi _).mp h

theorem ιmap_π : ιmap D g hg ≫ ProjSpace.π R (mm k n) = D.p := by
  refine Scheme.Cover.hom_ext (𝒰 D g hg) _ _ fun l => ?_
  change ((D.V (τ g l)).ι ≫ ιmap D g hg) ≫ ProjSpace.π R (mm k n) = (D.V (τ g l)).ι ≫ D.p
  rw [Vι_ιmap]
  unfold fV fS
  rw [Category.assoc, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, specMap_algebraMap_S, ← Category.assoc, sV_gS]

theorem ratio_eq_isLocalizationElem (l₀ l : Fin (mm k n + 1)) :
    ProjSpace.ratio R (mm k n) l₀ l =
      Away.isLocalizationElem (ProjSpace.X_mem_one R (mm k n) l₀) (ProjSpace.X_mem_one R (mm k n) l) := by
  apply HomogeneousLocalization.val_injective
  simp [ProjSpace.ratio, Away.val_mk]

theorem preimage_basicOpen (l : Fin (mm k n + 1)) :
    ιmap D g hg ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X l) = D.V (τ g l) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨l₀, hl₀⟩ := exists_mem_V_τ D g hg y
    rw [← SetLike.mem_coe, ← range_gS D (τ g l₀)] at hl₀
    obtain ⟨z, rfl⟩ := hl₀

    have hy' : (gS D (τ g l₀) ≫ ιmap D g hg).base z ∈ Proj.basicOpen 𝒜 (MvPolynomial.X l) := hy
    rw [gS_ιmap] at hy'
    unfold fS at hy'
    rw [Scheme.Hom.comp_base, TopCat.comp_app, ← Scheme.Hom.mem_preimage,
      Proj.awayι_preimage_basicOpen 𝒜 (ProjSpace.X_mem_one R (mm k n) l₀) one_pos
        (ProjSpace.X_mem_one R (mm k n) l) one_pos, ← ratio_eq_isLocalizationElem] at hy'
    change PrimeSpectrum.comap (ψ D g l₀).toRingHom z ∈ PrimeSpectrum.basicOpen _ at hy'
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, ψ_ratio] at hy'
    exact gS_mem_of_inChart D (τ g l₀) z (τ g l) (inChart_of_notMem D (τ g l₀) z (τ g l) hy')
  · intro y hy
    rw [← SetLike.mem_coe, ← range_gS D (τ g l)] at hy
    obtain ⟨z, rfl⟩ := hy
    change (gS D (τ g l) ≫ ιmap D g hg).base z ∈ Proj.basicOpen 𝒜 (MvPolynomial.X l)
    rw [gS_ιmap, ← Proj.opensRange_awayι 𝒜 (MvPolynomial.X l) (ProjSpace.X_mem_one R (mm k n) l) one_pos]
    unfold fS
    exact ⟨_, by rw [Scheme.Hom.comp_base, TopCat.comp_app]⟩

include hg in

theorem ψ_surjective (l : Fin (mm k n + 1)) : Function.Surjective (ψ D g l) := by
  haveI : IsOpenImmersion (D.pt (S D (τ g l)) (NS D (τ g l))).1 := by rw [pt_NS]; infer_instance
  have hgen := Module.Grassmannian.adjoin_eq_top_of_isOpenImmersion_of_opensRange_eq R M k D.Gr D.p D.pt D.hpt
    D.V D.hVchart (Fin (n + 1)) g hg (τ g l) (S D (τ g l)) (NS D (τ g l))
    (TopologicalSpace.Opens.ext (by
      change Set.range ((D.pt (S D (τ g l)) (NS D (τ g l))).1).base = _
      rw [pt_NS, range_gS]))
  rw [← AlgHom.range_eq_top, eq_top_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro s ⟨a', c, i, hc, rfl⟩
  refine ⟨ProjSpace.ratio R (mm k n) l ((ε k n).symm (Function.update (ε k n l) i a')), ?_⟩
  change ψ D g l _ = c i
  rw [ψ_ratio]
  unfold a
  rw [← update_τ]
  exact (eq_Pl_update (τ g l) (Nτ D g l) (g a') c hc i).symm

include hg in

theorem isClosedImmersion_ιmap : IsClosedImmersion (ιmap D g hg) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (ProjSpace.affineOpenCover R (mm k n)).openCover (fun l => ?_)

  have H : gS D (τ g l) ≫ ιmap D g hg =
      Spec.map (CommRingCat.ofHom (ψ D g l).toRingHom) ≫ awayιX (R := R) l :=
    gS_ιmap D g hg l
  have H' : ιmap D g hg ⁻¹ᵁ (awayιX (R := R) (k := k) (n := n) l).opensRange = (gS D (τ g l)).opensRange := by
    rw [Proj.opensRange_awayι, opensRange_gS, preimage_basicOpen]
  have hP := IsOpenImmersion.isPullback _ _ _ _ H H'
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ψ D g l).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (ψ_surjective D g hg l)
  change IsClosedImmersion (pullback.snd (ιmap D g hg) (awayιX (R := R) l))
  rw [← hP.flip.isoPullback_inv_snd]
  infer_instance

end glue

end GrassPluckerEmb
p2m_reactivate "P2MW.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents.GrassPluckerEmb"

theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ)
    (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      Module.Grassmannian A (A ⊗[R] M) k ≃
        {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (hpt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
    (V : (Fin k → M) → Gr.Opens) (hV : ⨆ x, V x = ⊤) (hVaff : ∀ x, IsAffineOpen (V x))
    (hVchart : ∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A]
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
        Function.Bijective fun v : Fin k → A =>
          ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)) :
    ∃ (m : ℕ) (ι : Gr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R m = p := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let g : Fin (n + 1) → M := Fin.cons 0 s
  have hg : Submodule.span R (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← hs]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, by simp [g]⟩
  let D : GrassPluckerEmb.Rep R M k := ⟨Gr, p, pt, hpt, V, hV, hVaff, hVchart⟩
  exact ⟨GrassPluckerEmb.mm k n, GrassPluckerEmb.ιmap D g hg, GrassPluckerEmb.isClosedImmersion_ιmap D g hg,
    GrassPluckerEmb.ιmap_π D g hg⟩

end S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents
end P2MW
export P2MW.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents (solution)
