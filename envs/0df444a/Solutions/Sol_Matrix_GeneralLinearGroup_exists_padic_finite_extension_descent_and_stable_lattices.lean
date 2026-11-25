-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_padic_finite_extension_descent_and_stable_lattices
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:00:10.725487+00:00
-- url     : https://prove2.me/submissions/46f7dc29-df9c-42b1-8fe9-48286174c71b

import Mathlib

/-!
# Descent of representations to a finite subextension, with stable lattices

A representation `ρ : Γ →* GL_r(L)` of a finitely generated group over an algebraic extension `L/K` has all its
matrix entries in one finite subextension `E` (the entries of `ρ` on a finite generating set and of their inverses
generate a finite extension). Every `ρ`-stable `L`-subspace `W` of `L^r` is spanned by its `E`-points (a finite
spanning set lies in `E^r` after enlarging `E`), and for finite `Γ` the `O_E`-span of the columns of all `ρ g`,
cut down to `W ∩ E^r`, is a `Γ`-stable finitely generated `O_E`-lattice spanning `W ∩ E^r` (here `K = ℚ_l`,
`L = Q̄_l`, `O_E` the integral closure of `ℤ_l` in `E`, a Dedekind domain with fraction field `E`).
-/

set_option autoImplicit false

open Matrix

namespace RamanujanPetersson.CoeffsDescentSol

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- D1: a finite subset of an algebraic extension lies in a finite intermediate extension. -/
theorem exists_fd_of_finite [Algebra.IsAlgebraic K L] (S : Set L) (hS : S.Finite) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧ S ⊆ E := by
  have : Finite S := hS.to_subtype
  exact ⟨IntermediateField.adjoin K S,
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
    IntermediateField.subset_adjoin K S⟩

variable {Γ : Type*} [Group Γ] {r : ℕ}

/-- `ρ` has all matrix entries in the intermediate field `E`. -/
def DefinedOver (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) : Prop :=
  ∀ g i j, (ρ g : Matrix (Fin r) (Fin r) L) i j ∈ E

theorem mul_entries_mem (E : IntermediateField K L) {A B : Matrix (Fin r) (Fin r) L}
    (hA : ∀ i j, A i j ∈ E) (hB : ∀ i j, B i j ∈ E) (i j : Fin r) : (A * B) i j ∈ E := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

/-- The elements `g` with `ρ g` and `ρ g⁻¹` both `E`-rational. -/
def entrySubgroup (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) : Subgroup Γ where
  carrier := {g | (∀ i j, (ρ g : Matrix (Fin r) (Fin r) L) i j ∈ E) ∧
    ∀ i j, (ρ g⁻¹ : Matrix (Fin r) (Fin r) L) i j ∈ E}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [map_mul, Units.val_mul]; exact mul_entries_mem E ha1 hb1 i j
    · rw [_root_.mul_inv_rev, map_mul, Units.val_mul]; exact mul_entries_mem E hb2 ha2 i j
  one_mem' := by
    have h1 : ∀ i j, ((1 : Matrix (Fin r) (Fin r) L) i j) ∈ E := fun i j => by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem E
      · exact zero_mem E
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [map_one, Units.val_one]; exact h1 i j
    · rw [inv_one, map_one, Units.val_one]; exact h1 i j
  inv_mem' := by
    rintro a ⟨h1, h2⟩
    refine ⟨h2, fun i j => ?_⟩
    rw [inv_inv]; exact h1 i j

/-- D2: `ρ` is `E`-rational as soon as the generators and their inverses are. -/
theorem definedOver_of_closure (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) {S : Set Γ}
    (hS : Subgroup.closure S = ⊤)
    (h : ∀ g ∈ S, (∀ i j, (ρ g : Matrix (Fin r) (Fin r) L) i j ∈ E) ∧
      ∀ i j, (ρ g⁻¹ : Matrix (Fin r) (Fin r) L) i j ∈ E) :
    DefinedOver ρ E := by
  have hle : Subgroup.closure S ≤ entrySubgroup ρ E := (Subgroup.closure_le _).2 h
  intro g i j
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  exact (hle hg).1 i j

/-- An `L`-matrix with entries known to lie in `E`, as an `E`-matrix. -/
def restrictMat (E : IntermediateField K L) (A : Matrix (Fin r) (Fin r) L) (h : ∀ i j, A i j ∈ E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i j => ⟨A i j, h i j⟩

theorem map_restrictMat (E : IntermediateField K L) (A : Matrix (Fin r) (Fin r) L) (h : ∀ i j, A i j ∈ E) :
    (restrictMat E A h).map (algebraMap E L) = A := by
  ext i j; rfl

theorem restrictMat_inj (E : IntermediateField K L) {A B : Matrix (Fin r) (Fin r) E}
    (h : A.map (algebraMap E L) = B.map (algebraMap E L)) : A = B :=
  Matrix.map_injective (algebraMap E L).injective h

/-- The `E`-matrices of an `E`-rational `ρ`. -/
def descendMat (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) (h : DefinedOver ρ E) :
    Γ →* Matrix (Fin r) (Fin r) E where
  toFun g := restrictMat E _ (h g)
  map_one' := restrictMat_inj E (by
    rw [map_restrictMat, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' a b := restrictMat_inj E (by
    simp only [Matrix.map_mul, map_restrictMat, map_mul, Units.val_mul])

/-- The descended representation `Γ →* GL_r(E)`. -/
def descend (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) (h : DefinedOver ρ E) :
    Γ →* GL (Fin r) E :=
  (descendMat ρ E h).toHomUnits

theorem descend_spec (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) (h : DefinedOver ρ E) (g : Γ) :
    ((descend ρ E h g : Matrix (Fin r) (Fin r) E)).map (algebraMap E L) = ρ g :=
  map_restrictMat E _ (h g)

/-- `R`-submodules of `F^r` stable under `ρ`. -/
def Stable {F : Type*} [Field F] (R : Type*) [CommRing R] [Algebra R F] (ρ : Γ →* GL (Fin r) F)
    (T : Submodule R (Fin r → F)) : Prop :=
  ∀ g v, v ∈ T → (ρ g : Matrix (Fin r) (Fin r) F) *ᵥ v ∈ T

/-- The coordinatewise inclusion `E^r → L^r`. -/
def incl (E : IntermediateField K L) : (Fin r → E) →ₗ[E] (Fin r → L) where
  toFun v i := (v i : L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_mulVec (E : IntermediateField K L) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    incl E (A *ᵥ v) = A.map (algebraMap E L) *ᵥ incl E v := by
  funext i; exact RingHom.map_mulVec (algebraMap E L) A v i

/-- The `E`-points `W ∩ E^r` of an `L`-subspace `W`. -/
def descendSub (E : IntermediateField K L) (W : Submodule L (Fin r → L)) : Submodule E (Fin r → E) :=
  (W.restrictScalars E).comap (incl E)

theorem mem_descendSub (E : IntermediateField K L) (W : Submodule L (Fin r → L)) (v : Fin r → E) :
    v ∈ descendSub E W ↔ incl E v ∈ W := Iff.rfl

theorem stable_descendSub (ρ : Γ →* GL (Fin r) L) (E : IntermediateField K L) (h : DefinedOver ρ E)
    (W : Submodule L (Fin r → L)) (hW : Stable L ρ W) : Stable E (descend ρ E h) (descendSub E W) := by
  intro g v hv
  rw [mem_descendSub, incl_mulVec, descend_spec]
  exact hW g _ hv

theorem span_descendSub (E : IntermediateField K L) (W : Submodule L (Fin r → L)) (s : Set (Fin r → L))
    (hs : Submodule.span L s = W) (hsE : ∀ v ∈ s, ∀ i, v i ∈ E) :
    Submodule.span L (incl E '' (descendSub E W : Set (Fin r → E))) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨v, hv, rfl⟩; exact hv
  · refine le_trans (le_of_eq hs.symm) (Submodule.span_mono ?_)
    intro v hv
    refine ⟨fun i => ⟨v i, hsE v hv i⟩, ?_, rfl⟩
    show v ∈ W
    rw [← hs]; exact Submodule.subset_span hv

/-- D3 (descent of a representation and of finitely many stable subspaces, e.g. a composition series). -/
theorem exists_descent [Algebra.IsAlgebraic K L] [Group.FG Γ] {m : ℕ} (ρ : Γ →* GL (Fin r) L)
    (W : Fin m → Submodule L (Fin r → L)) (hW : ∀ k, Stable L ρ (W k)) :
    ∃ (E : IntermediateField K L) (h : DefinedOver ρ E), FiniteDimensional K E ∧
      ∀ k, Stable E (descend ρ E h) (descendSub E (W k)) ∧
        Submodule.span L (incl E '' (descendSub E (W k) : Set (Fin r → E))) = W k := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.1 ‹Group.FG Γ›
  choose s hs using fun k => (IsNoetherian.noetherian (W k) :
    ∃ t : Finset (Fin r → L), Submodule.span L (t : Set (Fin r → L)) = W k)
  let T : Set L := (⋃ g ∈ S, ⋃ i, ⋃ j, ({(ρ g : Matrix (Fin r) (Fin r) L) i j,
      (ρ g⁻¹ : Matrix (Fin r) (Fin r) L) i j} : Set L)) ∪
      ⋃ k, ⋃ v ∈ (s k : Set (Fin r → L)), Set.range v
  have hT : T.Finite := by
    refine Set.Finite.union (hSfin.biUnion fun g _ => ?_)
      (Set.finite_iUnion fun k => (s k).finite_toSet.biUnion fun v _ => Set.finite_range v)
    exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.toFinite _
  obtain ⟨E, hE, hTE⟩ := exists_fd_of_finite (K := K) T hT
  have h : DefinedOver ρ E := by
    refine definedOver_of_closure ρ E hS fun g hg => ⟨fun i j => hTE ?_, fun i j => hTE ?_⟩
    · exact Or.inl (Set.mem_biUnion hg (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Or.inl rfl⟩⟩))
    · exact Or.inl (Set.mem_biUnion hg (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Or.inr rfl⟩⟩))
  refine ⟨E, h, hE, fun k => ⟨stable_descendSub ρ E h (W k) (hW k), ?_⟩⟩
  refine span_descendSub E (W k) _ (hs k) fun v hv i => hTE (Or.inr ?_)
  exact Set.mem_iUnion.2 ⟨k, Set.mem_biUnion hv ⟨i, rfl⟩⟩

end Field

section Lattice

variable {F : Type*} [Field F] (R : Type*) [CommRing R] [Algebra R F]
variable {Γ : Type*} [Group Γ] {r : ℕ}

/-- The `R`-span of the columns of all `ρ g`. -/
def orbitLattice (ρ : Γ →* GL (Fin r) F) : Submodule R (Fin r → F) :=
  Submodule.span R (Set.range fun p : Γ × Fin r =>
    (ρ p.1 : Matrix (Fin r) (Fin r) F) *ᵥ Pi.single p.2 1)

theorem orbitLattice_stable (ρ : Γ →* GL (Fin r) F) : Stable R ρ (orbitLattice R ρ) := by
  intro g v hv
  let f : (Fin r → F) →ₗ[R] (Fin r → F) := ((ρ g : Matrix (Fin r) (Fin r) F).mulVecLin).restrictScalars R
  have hle : orbitLattice R ρ ≤ (orbitLattice R ρ).comap f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, i⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span ⟨(g * a, i), ?_⟩
    simp only [f, map_mul, Units.val_mul, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec]
  exact hle hv

theorem orbitLattice_fg [Finite Γ] (ρ : Γ →* GL (Fin r) F) : (orbitLattice R ρ).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_orbitLattice (ρ : Γ →* GL (Fin r) F) :
    Submodule.span F (orbitLattice R ρ : Set (Fin r → F)) = ⊤ := by
  refine top_le_iff.1 ((Pi.basisFun F (Fin r)).span_eq.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  refine Submodule.subset_span ⟨(1, i), ?_⟩
  simp only [map_one, Units.val_one, Matrix.one_mulVec, Pi.basisFun_apply]

/-- The lattice of a stable subspace `W`: `orbitLattice ∩ W`. -/
def latticeIn (ρ : Γ →* GL (Fin r) F) (W : Submodule F (Fin r → F)) : Submodule R (Fin r → F) :=
  orbitLattice R ρ ⊓ W.restrictScalars R

theorem latticeIn_stable (ρ : Γ →* GL (Fin r) F) (W : Submodule F (Fin r → F)) (hW : Stable F ρ W) :
    Stable R ρ (latticeIn R ρ W) :=
  fun g _ hv => Submodule.mem_inf.2
    ⟨orbitLattice_stable R ρ g _ (Submodule.mem_inf.1 hv).1, hW g _ (Submodule.mem_inf.1 hv).2⟩

theorem latticeIn_fg [Finite Γ] [IsNoetherianRing R] (ρ : Γ →* GL (Fin r) F) (W : Submodule F (Fin r → F)) :
    (latticeIn R ρ W).FG :=
  (orbitLattice_fg R ρ).of_le inf_le_left

/-- Every vector in the `F`-span of an `R`-submodule has a nonzero `R`-multiple in it. -/
theorem exists_smul_mem [IsDomain R] [IsFractionRing R F] (T : Submodule R (Fin r → F)) {v : Fin r → F}
    (hv : v ∈ Submodule.span F (T : Set (Fin r → F))) : ∃ d : R, d ≠ 0 ∧ d • v ∈ T := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm d₂ d₁]
    rw [e]; exact T.add_mem (T.smul_mem d₂ h₁) (T.smul_mem d₁ h₂)
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨(b : R) * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, ?_⟩
    have key : ((b : R) * d) • (c • x) = a • (d • x) := by
      rw [← algebraMap_smul F ((b : R) * d), ← algebraMap_smul F a, ← algebraMap_smul F d, smul_smul,
        smul_smul, map_mul]
      congr 1
      simp only at hab
      rw [← hab]; ring
    rw [key]; exact T.smul_mem a h

theorem span_latticeIn [IsDomain R] [IsFractionRing R F] (ρ : Γ →* GL (Fin r) F) (W : Submodule F (Fin r → F)) :
    Submodule.span F (latticeIn R ρ W : Set (Fin r → F)) = W := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun v hv => (Submodule.mem_inf.1 hv).2
  · intro v hv
    have htop : v ∈ Submodule.span F (orbitLattice R ρ : Set (Fin r → F)) := by
      rw [span_orbitLattice]; exact Submodule.mem_top
    obtain ⟨d, hd, hdv⟩ := exists_smul_mem R (orbitLattice R ρ) htop
    have hd' : algebraMap R F d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hd
    have hmem : d • v ∈ latticeIn R ρ W := Submodule.mem_inf.2
      ⟨hdv, by rw [← algebraMap_smul F d v]; exact W.smul_mem _ hv⟩
    have : v = (algebraMap R F d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul F d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Lattice

section Main

theorem main
    (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [Group.FG Γ] (r m : ℕ)
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin r) (AlgebraicClosure ℚ_[l]))
    (W : Fin m → Submodule (AlgebraicClosure ℚ_[l]) (Fin r → AlgebraicClosure ℚ_[l]))
    (hW : ∀ (k : Fin m) (g : Γ) (v : Fin r → AlgebraicClosure ℚ_[l]), v ∈ W k →
      Matrix.mulVec (ρ g : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ_[l])) v ∈ W k) :
    ∃ (E : IntermediateField ℚ_[l] (AlgebraicClosure ℚ_[l]))
      (ρE : Γ →* Matrix.GeneralLinearGroup (Fin r) E),
      FiniteDimensional ℚ_[l] E ∧
      (∀ g : Γ, (ρE g : Matrix (Fin r) (Fin r) E).map (algebraMap E (AlgebraicClosure ℚ_[l])) =
        (ρ g : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ_[l]))) ∧
      ∀ k : Fin m,
        Submodule.span (AlgebraicClosure ℚ_[l])
            ((W k : Set (Fin r → AlgebraicClosure ℚ_[l])) ∩
              Set.range (fun (v : Fin r → E) (i : Fin r) => (v i : AlgebraicClosure ℚ_[l]))) = W k ∧
          (Finite Γ → ∃ Λ : Submodule (integralClosure ℤ_[l] E) (Fin r → E), Λ.FG ∧
            (∀ (g : Γ) (v : Fin r → E), v ∈ Λ →
              Matrix.mulVec (ρE g : Matrix (Fin r) (Fin r) E) v ∈ Λ) ∧
            ∀ v : Fin r → E, v ∈ Submodule.span E (Λ : Set (Fin r → E)) ↔
              (fun i : Fin r => (v i : AlgebraicClosure ℚ_[l])) ∈ W k) := by
  obtain ⟨E, h, hE, hk⟩ := exists_descent (K := ℚ_[l]) ρ W (fun k => hW k)
  refine ⟨E, descend ρ E h, hE, fun g => descend_spec ρ E h g, fun k => ⟨?_, fun hfin => ?_⟩⟩
  · have hset : (incl E '' (descendSub E (W k) : Set (Fin r → E))) =
        (W k : Set (Fin r → AlgebraicClosure ℚ_[l])) ∩
          Set.range (fun (v : Fin r → E) (i : Fin r) => (v i : AlgebraicClosure ℚ_[l])) := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hv, v, rfl⟩
      · rintro ⟨hw, v, rfl⟩
        exact ⟨v, hw, rfl⟩
    rw [← hset]
    exact (hk k).2
  · have : Algebra.IsSeparable ℚ_[l] E :=
      Algebra.isSeparable_tower_bot_of_isSeparable ℚ_[l] E (AlgebraicClosure ℚ_[l])
    have : IsFractionRing (integralClosure ℤ_[l] E) E :=
      integralClosure.isFractionRing_of_finite_extension ℚ_[l] E
    have : IsDedekindDomain (integralClosure ℤ_[l] E) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] E
    refine ⟨latticeIn (integralClosure ℤ_[l] E) (descend ρ E h) (descendSub E (W k)),
      latticeIn_fg _ _ _, latticeIn_stable _ _ _ (hk k).1, fun v => ?_⟩
    rw [span_latticeIn]
    exact Iff.rfl

end Main

end RamanujanPetersson.CoeffsDescentSol

theorem solution
    (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [Group.FG Γ] (r m : ℕ)
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin r) (AlgebraicClosure ℚ_[l]))
    (W : Fin m → Submodule (AlgebraicClosure ℚ_[l]) (Fin r → AlgebraicClosure ℚ_[l]))
    (hW : ∀ (k : Fin m) (g : Γ) (v : Fin r → AlgebraicClosure ℚ_[l]), v ∈ W k →
      Matrix.mulVec (ρ g : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ_[l])) v ∈ W k) :
    ∃ (E : IntermediateField ℚ_[l] (AlgebraicClosure ℚ_[l]))
      (ρE : Γ →* Matrix.GeneralLinearGroup (Fin r) E),
      FiniteDimensional ℚ_[l] E ∧
      (∀ g : Γ, (ρE g : Matrix (Fin r) (Fin r) E).map (algebraMap E (AlgebraicClosure ℚ_[l])) =
        (ρ g : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ_[l]))) ∧
      ∀ k : Fin m,
        Submodule.span (AlgebraicClosure ℚ_[l])
            ((W k : Set (Fin r → AlgebraicClosure ℚ_[l])) ∩
              Set.range (fun (v : Fin r → E) (i : Fin r) => (v i : AlgebraicClosure ℚ_[l]))) = W k ∧
          (Finite Γ → ∃ Λ : Submodule (integralClosure ℤ_[l] E) (Fin r → E), Λ.FG ∧
            (∀ (g : Γ) (v : Fin r → E), v ∈ Λ →
              Matrix.mulVec (ρE g : Matrix (Fin r) (Fin r) E) v ∈ Λ) ∧
            ∀ v : Fin r → E, v ∈ Submodule.span E (Λ : Set (Fin r → E)) ↔
              (fun i : Fin r => (v i : AlgebraicClosure ℚ_[l])) ∈ W k) := by
  exact RamanujanPetersson.CoeffsDescentSol.main l Γ r m ρ W hW
