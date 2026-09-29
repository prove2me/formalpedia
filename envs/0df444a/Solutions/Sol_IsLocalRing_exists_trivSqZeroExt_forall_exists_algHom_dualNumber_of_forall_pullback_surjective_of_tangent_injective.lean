-- Prove2me | solution 1 for IsLocalRing.exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1e0268b4-feec-5abf-a1fc-77f588103766

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace P2mSchlessingerTangent

open IsLocalRing

variable {O : Type u} [CommRing O] [IsLocalRing O]

section tsze

variable (O)
variable (M : Type u) [AddCommGroup M] [Module (ResidueField O) M] [Module (ResidueField O)ᵐᵒᵖ M]
  [IsCentralScalar (ResidueField O) M] [Module O M] [IsScalarTower O (ResidueField O) M]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ M]
variable (N : Type u) [AddCommGroup N] [Module (ResidueField O) N] [Module (ResidueField O)ᵐᵒᵖ N]
  [IsCentralScalar (ResidueField O) N] [Module O N] [IsScalarTower O (ResidueField O) N]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ N]
variable (P : Type u) [AddCommGroup P] [Module (ResidueField O) P] [Module (ResidueField O)ᵐᵒᵖ P]
  [IsCentralScalar (ResidueField O) P] [Module O P] [IsScalarTower O (ResidueField O) P]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ P]

abbrev resT : TrivSqZeroExt (ResidueField O) M →+* ResidueField O :=
  (TrivSqZeroExt.fstHom O (ResidueField O) M).toRingHom

theorem resT_apply (x : TrivSqZeroExt (ResidueField O) M) : resT O M x = x.fst := rfl

theorem resT_surjective : Function.Surjective (resT O M) := fun c => ⟨TrivSqZeroExt.inl c, rfl⟩

theorem resT_compat : (resT O M).comp (algebraMap O (TrivSqZeroExt (ResidueField O) M)) = residue O := rfl

theorem algebraMap_tsze (o : O) :
    algebraMap O (TrivSqZeroExt (ResidueField O) M) o = TrivSqZeroExt.inl (residue O o) := rfl

theorem isLocalRing_tsze : IsLocalRing (TrivSqZeroExt (ResidueField O) M) := by
  haveI : Nontrivial (TrivSqZeroExt (ResidueField O) M) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg TrivSqZeroExt.fst h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  by_cases h : x.fst = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
    exact isUnit_one
  · left
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact isUnit_iff_ne_zero.2 h

theorem isArtinianRing_tsze [Module.Finite (ResidueField O) M] :
    IsArtinianRing (TrivSqZeroExt (ResidueField O) M) :=
  haveI : Module.Finite (ResidueField O) (TrivSqZeroExt (ResidueField O) M) :=
    inferInstanceAs (Module.Finite (ResidueField O) (ResidueField O × M))
  IsArtinianRing.of_finite (ResidueField O) _

variable {M N P}

def mapO (f : M →ₗ[ResidueField O] N) :
    TrivSqZeroExt (ResidueField O) M →ₐ[O] TrivSqZeroExt (ResidueField O) N where
  toFun x := ((x.fst, f x.snd) : ResidueField O × N)
  map_one' := TrivSqZeroExt.ext rfl (by
    change f (TrivSqZeroExt.snd (1 : TrivSqZeroExt (ResidueField O) M)) = 0
    rw [TrivSqZeroExt.snd_one, map_zero])
  map_mul' x y := TrivSqZeroExt.ext rfl (by
    change f (x * y).snd = x.fst • f y.snd + MulOpposite.op y.fst • f x.snd
    rw [TrivSqZeroExt.snd_mul, map_add, LinearMap.map_smul, op_smul_eq_smul, op_smul_eq_smul,
      LinearMap.map_smul])
  map_zero' := TrivSqZeroExt.ext rfl (by
    change f (TrivSqZeroExt.snd (0 : TrivSqZeroExt (ResidueField O) M)) = 0
    rw [TrivSqZeroExt.snd_zero, map_zero])
  map_add' x y := TrivSqZeroExt.ext rfl (by
    change f (x + y).snd = f x.snd + f y.snd
    rw [TrivSqZeroExt.snd_add, map_add])
  commutes' o := TrivSqZeroExt.ext rfl (by
    change f (algebraMap O (TrivSqZeroExt (ResidueField O) M) o).snd =
      (algebraMap O (TrivSqZeroExt (ResidueField O) N) o).snd
    rw [algebraMap_tsze, algebraMap_tsze, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl, map_zero])

@[scoped simp] theorem fst_mapO (f : M →ₗ[ResidueField O] N) (x : TrivSqZeroExt (ResidueField O) M) :
    (mapO O f x).fst = x.fst := rfl

@[scoped simp] theorem snd_mapO (f : M →ₗ[ResidueField O] N) (x : TrivSqZeroExt (ResidueField O) M) :
    (mapO O f x).snd = f x.snd := rfl

theorem mapO_compat (f : M →ₗ[ResidueField O] N) : (resT O N).comp (mapO O f).toRingHom = resT O M := rfl

theorem mapO_comp (f : M →ₗ[ResidueField O] N) (g : N →ₗ[ResidueField O] P) :
    (mapO O g).comp (mapO O f) = mapO O (g ∘ₗ f) :=
  AlgHom.ext fun _ => rfl

theorem mapO_congr {f g : M →ₗ[ResidueField O] N} (h : f = g) : mapO O f = mapO O g := by rw [h]

def inlO : ResidueField O →ₐ[O] TrivSqZeroExt (ResidueField O) M :=
  { TrivSqZeroExt.inlHom (ResidueField O) M with
    commutes' := fun o => rfl }

theorem inlO_compat : (resT O M).comp (inlO O (M := M)).toRingHom = RingHom.id _ := rfl

variable (M) in

theorem exists_eq_mapO (θ : TrivSqZeroExt (ResidueField O) M →ₐ[O] DualNumber (ResidueField O))
    (hθ : (resT O (ResidueField O)).comp θ.toRingHom = resT O M) :
    ∃ f : M →ₗ[ResidueField O] ResidueField O, θ = mapO O f := by
  have hinl : ∀ c : ResidueField O, θ (TrivSqZeroExt.inl c) = TrivSqZeroExt.inl c := by
    intro c
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← algebraMap_tsze, AlgHom.commutes]; rfl
  have hfst : ∀ m : M, (θ (TrivSqZeroExt.inr m)).fst = 0 := by
    intro m
    change ((resT O (ResidueField O)).comp θ.toRingHom) (TrivSqZeroExt.inr m) = 0
    rw [hθ]; rfl
  let f : M →ₗ[ResidueField O] ResidueField O :=
    { toFun := fun m => (θ (TrivSqZeroExt.inr m)).snd
      map_add' := fun m m' => by rw [TrivSqZeroExt.inr_add, map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c m => by
        have : (TrivSqZeroExt.inr (c • m) : TrivSqZeroExt (ResidueField O) M) =
            TrivSqZeroExt.inl c * TrivSqZeroExt.inr m := (TrivSqZeroExt.inl_mul_inr c m).symm
        rw [this, map_mul, hinl, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
          smul_zero, add_zero]
        rfl }
  refine ⟨f, AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_⟩
  · change ((resT O (ResidueField O)).comp θ.toRingHom) x = x.fst
    rw [hθ]; rfl
  · have hx := TrivSqZeroExt.inl_fst_add_inr_snd_eq x
    conv_lhs => rw [← hx, map_add, hinl, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add]
    rfl

end tsze

section models

variable (O)

abbrev D : Type u := DualNumber (ResidueField O)
abbrev D₂ : Type u := TrivSqZeroExt (ResidueField O) (ResidueField O × ResidueField O)

abbrev resD : D O →+* ResidueField O := resT O (ResidueField O)

abbrev p₁ : D₂ O →ₐ[O] D O := mapO O (LinearMap.fst (ResidueField O) (ResidueField O) (ResidueField O))
abbrev p₂ : D₂ O →ₐ[O] D O := mapO O (LinearMap.snd (ResidueField O) (ResidueField O) (ResidueField O))
abbrev σ : D₂ O →ₐ[O] D O :=
  mapO O (LinearMap.fst (ResidueField O) (ResidueField O) (ResidueField O) +
    LinearMap.snd (ResidueField O) (ResidueField O) (ResidueField O))

theorem p_inj (b₁ b₂ : D₂ O) (h1 : p₁ O b₁ = p₁ O b₂) (h2 : p₂ O b₁ = p₂ O b₂) : b₁ = b₂ := by
  refine TrivSqZeroExt.ext (by simpa using congrArg TrivSqZeroExt.fst h1) (Prod.ext ?_ ?_)
  · simpa using congrArg TrivSqZeroExt.snd h1
  · simpa using congrArg TrivSqZeroExt.snd h2

theorem p_surj (t₁ t₂ : D O) (h : t₁.fst = t₂.fst) : ∃ b : D₂ O, p₁ O b = t₁ ∧ p₂ O b = t₂ :=
  ⟨TrivSqZeroExt.inl t₁.fst + TrivSqZeroExt.inr (t₁.snd, t₂.snd),
    TrivSqZeroExt.ext (by simp) (by simp),
    TrivSqZeroExt.ext (by simp [h]) (by simp)⟩

theorem snd_σ (b : D₂ O) : (σ O b).snd = (p₁ O b).snd + (p₂ O b).snd := rfl

abbrev μ (c : ResidueField O) : D O →ₐ[O] D O := mapO O (c • LinearMap.id)

theorem snd_μ (c : ResidueField O) (t : D O) : (μ O c t).snd = c * t.snd := rfl

end models

structure Datum (O : Type u) [CommRing O] [IsLocalRing O] where
  F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u
  Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
    F A resA → F A resA → Prop
  hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x : F A resA), Frel x x
  hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x y : F A resA), Frel x y → Frel y x
  htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x y z : F A resA), Frel x y → Frel y z → Frel x z
  Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA'
  Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
    Frel x y → Frel (Fmap f hf x) (Fmap f hf y)
  Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x
  Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
    (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
    (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
    (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x))

  x₀ : F (ResidueField O) (RingHom.id (ResidueField O))
  hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀
  hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
      (resB : B →+* ResidueField O), Function.Surjective resB →
      resB.comp (algebraMap O B) = residue O →
    ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
      (resA' : A' →+* ResidueField O), Function.Surjective resA' →
      resA'.comp (algebraMap O A') = residue O →
    ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
      (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
      resA''.comp (algebraMap O A'') = residue O →
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
      (resA : A →+* ResidueField O), Function.Surjective resA →
      resA.comp (algebraMap O A) = residue O →
    ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
      (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
      (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
      (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
      q'.comp p' = q''.comp p'' →
      (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
      Function.Surjective q'' →
      ∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
        ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x''

  r : ℕ
  e : F (DualNumber (ResidueField O))
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom → (Fin r → ResidueField O)
  he_rel : ∀ x y, Frel x y → e x = e y
  he_inj : ∀ x y, e x = e y → Frel x y
  he_smul : ∀ (c : ResidueField O)
      (μ : DualNumber (ResidueField O) →ₐ[O] DualNumber (ResidueField O))
      (hμ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp μ.toRingHom =
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
      (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
      ∀ x, e (Fmap μ hμ x) = c • e x
  he_add : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
      (resB : B →+* ResidueField O), Function.Surjective resB →
      resB.comp (algebraMap O B) = residue O →
      ∀ (p₁ p₂ σ : B →ₐ[O] DualNumber (ResidueField O))
        (hp₁ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          p₁.toRingHom = resB)
        (hp₂ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          p₂.toRingHom = resB)
        (hσ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          σ.toRingHom = resB),
      (∀ b₁ b₂ : B, p₁ b₁ = p₁ b₂ → p₂ b₁ = p₂ b₂ → b₁ = b₂) →
      (∀ t₁ t₂ : DualNumber (ResidueField O), TrivSqZeroExt.fst t₁ = TrivSqZeroExt.fst t₂ →
          ∃ b : B, p₁ b = t₁ ∧ p₂ b = t₂) →
      (∀ b : B, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
      ∀ y : F B resB, e (Fmap σ hσ y) = e (Fmap p₁ hp₁ y) + e (Fmap p₂ hp₂ y)

variable (S : Datum O)

namespace Datum

theorem Fmap_congr {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f f' : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (hf' : resA'.comp f'.toRingHom = resA)
    (h : f = f') (x : S.F A resA) : S.Fmap f hf x = S.Fmap f' hf' x := by
  subst h; rfl

theorem e_Fmap_comp {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (g : A' →ₐ[O] D O) (hf : resA'.comp f.toRingHom = resA)
    (hg : (resD O).comp g.toRingHom = resA') (h : A →ₐ[O] D O) (hh : (resD O).comp h.toRingHom = resA)
    (hgf : g.comp f = h) (x : S.F A resA) : S.e (S.Fmap g hg (S.Fmap f hf x)) = S.e (S.Fmap h hh x) := by
  subst hgf
  exact S.he_rel _ _ (S.hsymm _ _ (S.Fmap_comp f g hf hg hh x))

section lin

variable {M : Type u} [AddCommGroup M] [Module (ResidueField O) M] [Module (ResidueField O)ᵐᵒᵖ M]
  [IsCentralScalar (ResidueField O) M] [Module O M] [IsScalarTower O (ResidueField O) M]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ M]

def Λf (y : S.F (TrivSqZeroExt (ResidueField O) M) (resT O M)) (f : M →ₗ[ResidueField O] ResidueField O) :
    Fin S.r → ResidueField O :=
  S.e (S.Fmap (mapO O f) (mapO_compat O f) y)

theorem Λf_add (y : S.F (TrivSqZeroExt (ResidueField O) M) (resT O M))
    (f g : M →ₗ[ResidueField O] ResidueField O) : S.Λf y (f + g) = S.Λf y f + S.Λf y g := by
  haveI := isLocalRing_tsze O (ResidueField O × ResidueField O)
  haveI := isArtinianRing_tsze O (ResidueField O × ResidueField O)
  let φ : TrivSqZeroExt (ResidueField O) M →ₐ[O] D₂ O := mapO O (f.prod g)
  have key := S.he_add (D₂ O) (resT O _) (resT_surjective O _) (resT_compat O _) (p₁ O) (p₂ O) (σ O) rfl rfl
    rfl (p_inj O) (p_surj O) (snd_σ O) (S.Fmap φ (mapO_compat O _) y)
  unfold Λf
  rw [S.e_Fmap_comp φ (σ O) (mapO_compat O _) rfl (mapO O (f + g)) (mapO_compat O _) ?_,
    S.e_Fmap_comp φ (p₁ O) (mapO_compat O _) rfl (mapO O f) (mapO_compat O _) ?_,
    S.e_Fmap_comp φ (p₂ O) (mapO_compat O _) rfl (mapO O g) (mapO_compat O _) ?_] at key
  · exact key
  · rw [mapO_comp]; exact mapO_congr O (LinearMap.snd_prod f g)
  · rw [mapO_comp]; exact mapO_congr O (LinearMap.fst_prod f g)
  · rw [mapO_comp]; apply mapO_congr; rw [LinearMap.add_comp, LinearMap.fst_prod,
      LinearMap.snd_prod]

theorem Λf_smul (y : S.F (TrivSqZeroExt (ResidueField O) M) (resT O M)) (c : ResidueField O)
    (f : M →ₗ[ResidueField O] ResidueField O) : S.Λf y (c • f) = c • S.Λf y f := by
  have key := S.he_smul c (μ O c) rfl (snd_μ O c) (S.Fmap (mapO O f) (mapO_compat O f) y)
  unfold Λf
  rw [S.e_Fmap_comp (mapO O f) (μ O c) (mapO_compat O f) rfl (mapO O (c • f)) (mapO_compat O _) ?_] at key
  · exact key
  · rw [mapO_comp]; apply mapO_congr; rw [LinearMap.smul_comp, LinearMap.id_comp]

def Λ (y : S.F (TrivSqZeroExt (ResidueField O) M) (resT O M)) :
    (M →ₗ[ResidueField O] ResidueField O) →ₗ[ResidueField O] (Fin S.r → ResidueField O) where
  toFun := S.Λf y
  map_add' := S.Λf_add y
  map_smul' := S.Λf_smul y

theorem Λ_apply (y : S.F (TrivSqZeroExt (ResidueField O) M) (resT O M))
    (f : M →ₗ[ResidueField O] ResidueField O) : S.Λ y f = S.e (S.Fmap (mapO O f) (mapO_compat O f) y) :=
  rfl

end lin

def xD : S.F (D O) (resD O) := S.Fmap (inlO O) (inlO_compat O) S.x₀

def T : Submodule (ResidueField O) (Fin S.r → ResidueField O) where
  carrier := {v | ∃ x, S.e x = v}
  zero_mem' := by
    exact ⟨S.Fmap (μ O 0) rfl S.xD, (S.he_smul 0 (μ O 0) rfl (snd_μ O 0) S.xD).trans (zero_smul _ _)⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    haveI := isLocalRing_tsze O (ResidueField O × ResidueField O)
    haveI := isArtinianRing_tsze O (ResidueField O × ResidueField O)
    haveI := isLocalRing_tsze O (ResidueField O)
    haveI := isArtinianRing_tsze O (ResidueField O)

    have hcart : ∀ (a' a'' : D O), TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) a' =
        TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) a'' → ∃! b : D₂ O, p₁ O b = a' ∧ p₂ O b = a'' := by
      intro a' a'' h
      obtain ⟨b, hb⟩ := p_surj O a' a'' h
      exact ⟨b, hb, fun b' hb' => p_inj O _ _ (hb'.1.trans hb.1.symm) (hb'.2.trans hb.2.symm)⟩
    obtain ⟨w, hw₁, hw₂⟩ := S.hglue (D₂ O) (resT O _) (resT_surjective O _) (resT_compat O _)
      (D O) (resD O) (resT_surjective O _) (resT_compat O _)
      (D O) (resD O) (resT_surjective O _) (resT_compat O _)
      (ResidueField O) (RingHom.id _) Function.surjective_id rfl
      (p₁ O) rfl (p₂ O) rfl (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)) rfl
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)) rfl rfl hcart (resT_surjective O _)
      x y (S.htrans _ _ _ (S.hx₀ _) (S.hsymm _ _ (S.hx₀ _)))
    refine ⟨S.Fmap (σ O) rfl w, ?_⟩
    have e1 : S.e (S.Fmap (p₁ O) rfl w) = S.e x := S.he_rel _ _ hw₁
    have e2 : S.e (S.Fmap (p₂ O) rfl w) = S.e y := S.he_rel _ _ hw₂
    have key : S.e (S.Fmap (σ O) rfl w) = S.e (S.Fmap (p₁ O) rfl w) + S.e (S.Fmap (p₂ O) rfl w) :=
      S.he_add (D₂ O) (resT O _) (resT_surjective O _) (resT_compat O _) (p₁ O) (p₂ O) (σ O) rfl rfl rfl
        (p_inj O) (p_surj O) (snd_σ O) w
    rw [e1, e2] at key
    exact key
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨S.Fmap (μ O c) rfl x, S.he_smul c (μ O c) rfl (snd_μ O c) x⟩

theorem mem_T (x : S.F (D O) (resD O)) : S.e x ∈ S.T := ⟨x, rfl⟩

def d : ℕ := Module.finrank (ResidueField O) S.T

def basisT : Module.Basis (Fin S.d) (ResidueField O) S.T := Module.finBasis (ResidueField O) S.T

def xb (i : Fin S.d) : S.F (D O) (resD O) := (S.basisT i).2.choose

theorem e_xb (i : Fin S.d) : S.e (S.xb i) = (S.basisT i : Fin S.r → ResidueField O) :=
  (S.basisT i).2.choose_spec

theorem Fmap_comp' {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
    (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
    (hg : resA''.comp g.toRingHom = resA') (h : A →ₐ[O] A'') (hh : resA''.comp h.toRingHom = resA)
    (hgf : g.comp f = h) (x : S.F A resA) : S.Frel (S.Fmap h hh x) (S.Fmap g hg (S.Fmap f hf x)) := by
  subst hgf; exact S.Fmap_comp f g hf hg hh x

section fin

variable (O)

abbrev V (j : ℕ) : Type u := Fin j → ResidueField O
abbrev Tj (j : ℕ) : Type u := TrivSqZeroExt (ResidueField O) (V O j)

abbrev pr {j : ℕ} (i : Fin j) : Tj O j →ₐ[O] D O := mapO O (LinearMap.proj i)
abbrev rest (j : ℕ) : Tj O (j + 1) →ₐ[O] Tj O j :=
  mapO O (LinearMap.funLeft (ResidueField O) (ResidueField O) Fin.castSucc)
abbrev plast (j : ℕ) : Tj O (j + 1) →ₐ[O] D O := pr O (Fin.last j)

theorem pr_comp_rest {j : ℕ} (i : Fin j) : (pr O i).comp (rest O j) = pr O (Fin.castSucc i) := by
  rw [mapO_comp]; rfl

theorem cart_fin (j : ℕ) (a' : Tj O j) (a'' : D O)
    (h : TrivSqZeroExt.fstHom O (ResidueField O) (V O j) a' =
      TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) a'') :
    ∃! b : Tj O (j + 1), rest O j b = a' ∧ plast O j b = a'' := by
  change a'.fst = a''.fst at h
  let v : V O (j + 1) := Fin.snoc (α := fun _ => ResidueField O) a'.snd a''.snd
  have hv₁ : ∀ i : Fin j, v (Fin.castSucc i) = a'.snd i := fun i =>
    Fin.snoc_castSucc (α := fun _ => ResidueField O) _ _ i
  have hv₂ : v (Fin.last j) = a''.snd := Fin.snoc_last (α := fun _ => ResidueField O) _ _
  refine ⟨((a'.fst, v) : ResidueField O × V O (j + 1)), ⟨?_, ?_⟩, ?_⟩
  · exact TrivSqZeroExt.ext rfl (funext fun i => hv₁ i)
  · exact TrivSqZeroExt.ext h hv₂
  · rintro b ⟨hb₁, hb₂⟩
    refine TrivSqZeroExt.ext ?_ (funext fun i => ?_)
    · have := congrArg TrivSqZeroExt.fst hb₁; exact this
    · change b.snd i = v i
      induction i using Fin.lastCases with
      | last => rw [hv₂]; have := congrArg TrivSqZeroExt.snd hb₂; exact this
      | cast i => rw [hv₁]; have := congrArg TrivSqZeroExt.snd hb₁; exact congrFun this i

end fin

theorem glueFin : ∀ (j : ℕ) (x : Fin j → S.F (D O) (resD O)),
    ∃ ξ : S.F (Tj O j) (resT O (V O j)), ∀ i, S.Frel (S.Fmap (pr O i) (mapO_compat O _) ξ) (x i)
  | 0, _ => ⟨S.Fmap (inlO O) (inlO_compat O) S.x₀, fun i => i.elim0⟩
  | j + 1, x => by
    obtain ⟨ξ, hξ⟩ := glueFin j (fun i => x (Fin.castSucc i))
    haveI := isLocalRing_tsze O (V O (j + 1))
    haveI := isArtinianRing_tsze O (V O (j + 1))
    haveI := isLocalRing_tsze O (V O j)
    haveI := isArtinianRing_tsze O (V O j)
    haveI := isLocalRing_tsze O (ResidueField O)
    haveI := isArtinianRing_tsze O (ResidueField O)
    obtain ⟨ξ', h₁, h₂⟩ := S.hglue (Tj O (j + 1)) (resT O _) (resT_surjective O _) (resT_compat O _)
      (Tj O j) (resT O _) (resT_surjective O _) (resT_compat O _)
      (D O) (resD O) (resT_surjective O _) (resT_compat O _)
      (ResidueField O) (RingHom.id _) Function.surjective_id rfl
      (rest O j) rfl (plast O j) rfl (TrivSqZeroExt.fstHom O (ResidueField O) (V O j)) rfl
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)) rfl rfl (cart_fin O j) (resT_surjective O _)
      ξ (x (Fin.last j)) (S.htrans _ _ _ (S.hx₀ _) (S.hsymm _ _ (S.hx₀ _)))
    refine ⟨ξ', fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => exact h₂
    | cast i =>
      have c1 := S.Fmap_comp' (rest O j) (pr O i) rfl (mapO_compat O _) (pr O (Fin.castSucc i))
        (mapO_compat O _) (pr_comp_rest O i) ξ'
      exact S.htrans _ _ _ c1 (S.htrans _ _ _ (S.Fmap_rel (pr O i) (mapO_compat O _) _ _ h₁) (hξ i))

def ξU : S.F (Tj O S.d) (resT O (V O S.d)) := (S.glueFin S.d S.xb).choose

theorem ξU_spec (i : Fin S.d) : S.Frel (S.Fmap (pr O i) (mapO_compat O _) S.ξU) (S.xb i) :=
  (S.glueFin S.d S.xb).choose_spec i

theorem Λ_proj (i : Fin S.d) :
    S.Λ S.ξU (LinearMap.proj i) = (S.basisT i : Fin S.r → ResidueField O) :=
  (S.he_rel _ _ (S.ξU_spec i)).trans (S.e_xb i)

abbrev fc (c : Fin S.d → ResidueField O) : V O S.d →ₗ[ResidueField O] ResidueField O :=
  ∑ i, c i • LinearMap.proj i

theorem fc_single (c : Fin S.d → ResidueField O) (i : Fin S.d) : S.fc c (Pi.single i 1) = c i := by
  simp [LinearMap.sum_apply, Pi.single_apply]

theorem eq_fc (f : V O S.d →ₗ[ResidueField O] ResidueField O) : f = S.fc fun i => f (Pi.single i 1) := by
  apply LinearMap.pi_ext'
  intro i
  apply LinearMap.ext_ring
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.coe_single, fc_single]

theorem Λ_fc (c : Fin S.d → ResidueField O) : S.Λ S.ξU (S.fc c) = S.T.subtype (S.basisT.equivFun.symm c) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, Λ_proj]
  rfl

theorem surj (x : S.F (D O) (resD O)) :
    ∃ (θ : Tj O S.d →ₐ[O] D O) (hθ : (resD O).comp θ.toRingHom = resT O (V O S.d)),
      S.Frel (S.Fmap θ hθ S.ξU) x := by
  let v : S.T := ⟨S.e x, S.mem_T x⟩
  refine ⟨mapO O (S.fc (S.basisT.equivFun v)), mapO_compat O _, S.he_inj _ _ ?_⟩
  change S.Λ S.ξU (S.fc (S.basisT.equivFun v)) = S.e x
  rw [Λ_fc, LinearEquiv.symm_apply_apply]
  rfl

theorem inj (θ θ' : Tj O S.d →ₐ[O] D O) (hθ : (resD O).comp θ.toRingHom = resT O (V O S.d))
    (hθ' : (resD O).comp θ'.toRingHom = resT O (V O S.d))
    (h : S.Frel (S.Fmap θ hθ S.ξU) (S.Fmap θ' hθ' S.ξU)) : θ = θ' := by
  obtain ⟨f, rfl⟩ := exists_eq_mapO O (V O S.d) θ hθ
  obtain ⟨f', rfl⟩ := exists_eq_mapO O (V O S.d) θ' hθ'
  have h1 : S.Λ S.ξU f = S.Λ S.ξU f' := S.he_rel _ _ h
  rw [S.eq_fc f, S.eq_fc f', Λ_fc, Λ_fc] at h1
  have h2 := S.basisT.equivFun.symm.injective (S.T.subtype_injective h1)
  rw [S.eq_fc f, S.eq_fc f', h2]

end Datum

end P2mSchlessingerTangent
p2m_reactivate "P2MW.S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerTangent"

open IsLocalRing in
theorem solution
    (O : Type u) [CommRing O] [IsLocalRing O]
    (F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u)
    (Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
      F A resA → F A resA → Prop)
    (hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x : F A resA), Frel x x)
    (hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y : F A resA), Frel x y → Frel y x)
    (htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y z : F A resA), Frel x y → Frel y z → Frel x z)
    (Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA')
    (Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
      Frel x y → Frel (Fmap f hf x) (Fmap f hf y))
    (Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x)
    (Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
      (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
      (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
      (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x)))

    (x₀ : F (ResidueField O) (RingHom.id (ResidueField O)))
    (hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀)

    (hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O), Function.Surjective resA' →
        resA'.comp (algebraMap O A') = residue O →
      ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
        (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
        resA''.comp (algebraMap O A'') = residue O →
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
        (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
        (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
        (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
        q'.comp p' = q''.comp p'' →
        (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
        Function.Surjective q'' →
        ∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
          ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'')

    (r : ℕ)
    (e : F (DualNumber (ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom → (Fin r → ResidueField O))
    (he_rel : ∀ x y, Frel x y → e x = e y)
    (he_inj : ∀ x y, e x = e y → Frel x y)
    (he_smul : ∀ (c : ResidueField O)
        (μ : DualNumber (ResidueField O) →ₐ[O] DualNumber (ResidueField O))
        (hμ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp μ.toRingHom =
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ x, e (Fmap μ hμ x) = c • e x)
    (he_add : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
        ∀ (p₁ p₂ σ : B →ₐ[O] DualNumber (ResidueField O))
          (hp₁ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₁.toRingHom = resB)
          (hp₂ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₂.toRingHom = resB)
          (hσ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            σ.toRingHom = resB),
        (∀ b₁ b₂ : B, p₁ b₁ = p₁ b₂ → p₂ b₁ = p₂ b₂ → b₁ = b₂) →
        (∀ t₁ t₂ : DualNumber (ResidueField O), TrivSqZeroExt.fst t₁ = TrivSqZeroExt.fst t₂ →
            ∃ b : B, p₁ b = t₁ ∧ p₂ b = t₂) →
        (∀ b : B, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ y : F B resB, e (Fmap σ hσ y) = e (Fmap p₁ hp₁ y) + e (Fmap p₂ hp₂ y)) :
    ∃ (d : ℕ) (ξ : F (TrivSqZeroExt (ResidueField O) (Fin d → ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom),
      (∀ x : F (DualNumber (ResidueField O)) (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom,
        ∃ (θ : TrivSqZeroExt (ResidueField O) (Fin d → ResidueField O) →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom),
          Frel (Fmap θ hθ ξ) x) ∧
      (∀ (θ θ' : TrivSqZeroExt (ResidueField O) (Fin d → ResidueField O) →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom)
          (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
            (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom),
        Frel (Fmap θ hθ ξ) (Fmap θ' hθ' ξ) → θ = θ') := by
  let S : P2mSchlessingerTangent.Datum O :=
    { F := F, Frel := Frel, hrefl := hrefl, hsymm := hsymm, htrans := htrans, Fmap := Fmap,
      Fmap_rel := Fmap_rel, Fmap_id := Fmap_id, Fmap_comp := Fmap_comp, x₀ := x₀, hx₀ := hx₀,
      hglue := hglue, r := r, e := e, he_rel := he_rel, he_inj := he_inj, he_smul := he_smul,
      he_add := he_add }
  exact ⟨S.d, S.ξU, S.surj, S.inj⟩

end
end S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
end P2MW
export P2MW.S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective (solution)
