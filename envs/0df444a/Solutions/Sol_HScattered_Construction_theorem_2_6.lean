-- Prove2me | solution 1 for HScattered.Construction.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T08:09:23.847899+00:00
-- url     : https://prove2.me/submissions/289c868d-a287-492f-ae68-da75b427df8f

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered

set_option autoImplicit false

namespace HScatteredE00

open Module

/-- Lemma A: every `K`-subspace of dimension at most `h` meets `U` in `F`-dimension at most its
`K`-dimension. -/
theorem lemA {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [FiniteDimensional K V] [FiniteDimensional F V]
    (h : ℕ) (U : Submodule F V) (hhr : h < finrank K V)
    (hspan : Submodule.span K (U : Set V) = ⊤)
    (hsc : ∀ S : Submodule K V, finrank K S = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ h) :
    ∀ j : ℕ, ∀ S : Submodule K V, finrank K S + j = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ finrank K S := by
  intro j
  induction j with
  | zero =>
    intro S hS
    simp only [add_zero] at hS
    rw [hS]; exact hsc S hS
  | succ j ih =>
    intro S hS
    have hnot : ¬ (U : Set V) ⊆ S := by
      intro hsub
      have h1 : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hsub
      rw [hspan] at h1
      have h2 : S = ⊤ := top_le_iff.mp h1
      rw [h2, finrank_top] at hS
      omega
    obtain ⟨u, huU, huS⟩ := Set.not_subset.mp hnot
    have hS' : finrank K ↥(S ⊔ Submodule.span K {u}) = finrank K S + 1 :=
      Submodule.finrank_sup_span_singleton huS
    have hih := ih (S ⊔ Submodule.span K {u}) (by omega)
    have hlt : S.restrictScalars F ⊓ U < (S ⊔ Submodule.span K {u}).restrictScalars F ⊓ U := by
      rw [SetLike.lt_iff_le_and_exists]
      refine ⟨?_, u, ?_, ?_⟩
      · intro x hx
        rw [Submodule.mem_inf] at hx ⊢
        exact ⟨Submodule.mem_sup_left hx.1, hx.2⟩
      · rw [Submodule.mem_inf]
        exact ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self u), huU⟩
      · intro hx
        rw [Submodule.mem_inf] at hx
        exact huS hx.1
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

/-- Lemma B: an `F`-independent family in `U` with at most `h + 1` members is `K`-independent. -/
theorem lemB {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [FiniteDimensional K V] [FiniteDimensional F V]
    (h : ℕ) (U : Submodule F V) (hhr : h < finrank K V)
    (hspan : Submodule.span K (U : Set V) = ⊤)
    (hsc : ∀ S : Submodule K V, finrank K S = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ h)
    {d : ℕ} (hd : d ≤ h + 1) (w : Fin d → V) (hwU : ∀ i, w i ∈ U)
    (hw : LinearIndependent F w) : LinearIndependent K w := by
  by_contra hK
  set S : Submodule K V := Submodule.span K (Set.range w) with hSdef
  have hle : finrank K S ≤ d := by
    have := finrank_range_le_card (R := K) w
    simp only [Fintype.card_fin] at this
    exact this
  have hne : finrank K S ≠ d := by
    intro heq
    apply hK
    rw [linearIndependent_iff_card_eq_finrank_span]
    simp only [Fintype.card_fin]
    exact heq.symm
  have hA := lemA h U hhr hspan hsc (h - finrank K S) S (by omega)
  have hFd : finrank F ↥(Submodule.span F (Set.range w)) = d := by
    have := finrank_span_eq_card hw
    simpa using this
  have hsub : Submodule.span F (Set.range w) ≤ S.restrictScalars F ⊓ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, hwU i⟩
    show w i ∈ S
    exact Submodule.subset_span ⟨i, rfl⟩
  have := Submodule.finrank_mono hsub
  omega

/-- Injectivity of `u ↦ ∑ λᵢ uᵢ` on `U^m` for `F`-independent `λ` and `m ≤ h + 1`. -/
theorem lemC {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [FiniteDimensional K V] [FiniteDimensional F V]
    (h : ℕ) (U : Submodule F V) (hhr : h < finrank K V)
    (hspan : Submodule.span K (U : Set V) = ⊤)
    (hsc : ∀ S : Submodule K V, finrank K S = h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ h)
    {m : ℕ} (hm : m ≤ h + 1) (lam : Fin m → K) (hlam : LinearIndependent F lam)
    (u : Fin m → V) (huU : ∀ i, u i ∈ U) (hsum : ∑ i, lam i • u i = 0) :
    ∀ i, u i = 0 := by
  set W : Submodule F V := Submodule.span F (Set.range u) with hWdef
  have hWU : W ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact huU i
  have huW : ∀ i, u i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let b := Module.finBasis F W
  have hdW : finrank F W ≤ m := by
    have := finrank_range_le_card (R := F) u
    simp only [Fintype.card_fin] at this
    exact this
  let w : Fin (finrank F W) → V := fun j => (b j : V)
  have hwF : LinearIndependent F w :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hwK : LinearIndependent K w :=
    lemB h U hhr hspan hsc (by omega) w (fun j => hWU (b j).2) hwF
  -- coordinates
  let a : Fin m → Fin (finrank F W) → F := fun i j => b.repr ⟨u i, huW i⟩ j
  have hu : ∀ i, u i = ∑ j, a i j • w j := by
    intro i
    have := b.sum_repr ⟨u i, huW i⟩
    have h2 := congrArg W.subtype this
    simp only [map_sum, map_smul, Submodule.subtype_apply] at h2
    exact h2.symm
  have hsum2 : ∑ j, (∑ i, a i j • lam i) • w j = 0 := by
    rw [← hsum]
    simp_rw [hu, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_assoc, smul_comm]
  have hcoef : ∀ j, ∑ i, a i j • lam i = 0 :=
    Fintype.linearIndependent_iff.mp hwK _ hsum2
  have ha : ∀ i j, a i j = 0 := by
    intro i j
    exact Fintype.linearIndependent_iff.mp hlam (fun i => a i j) (hcoef j) i
  intro i
  rw [hu i]
  simp [ha]


theorem bound {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : HScattered.Bound.IsHScattered F K h U)
    (hn : h + 1 ≤ finrank F K) :
    (h + 1) * finrank F U ≤ finrank K V * finrank F K := by
  obtain ⟨hh0, hhr, hspan, hsc⟩ := hU
  have : FiniteDimensional F K := Module.Finite.of_finite
  have : FiniteDimensional F V := Module.Finite.trans K V
  have hFV : finrank F V = finrank F K * finrank K V := (Module.finrank_mul_finrank F K V).symm
  let bK := Module.finBasis F K
  let lam : Fin (h + 1) → K := fun i => bK (Fin.castLE hn i)
  have hlam : LinearIndependent F lam :=
    bK.linearIndependent.comp _ (Fin.castLE_injective hn)
  let ψ : (Fin (h + 1) → U) →ₗ[F] V :=
    { toFun := fun x => ∑ i, lam i • (x i : V)
      map_add' := by
        intro x y
        simp [smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_comm] }
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := lemC h U hhr hspan hsc le_rfl lam hlam (fun i => (x i : V)) (fun i => (x i).2) hx
    funext i
    exact Subtype.ext (this i)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, hFV] at this
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm] using this


end HScatteredE00

open HScatteredE00
open Module Polynomial

section frob

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]

/-- `x ↦ x ^ (q ^ j)` as an `F`-linear map. -/
noncomputable def frobJ (j : ℕ) : K →ₗ[F] K :=
  ((FiniteField.frobeniusAlgHom F K) ^ j).toLinearMap

theorem frobJ_apply (j : ℕ) (x : K) : frobJ F K j x = x ^ (Fintype.card F ^ j) := by
  induction j generalizing x with
  | zero => simp [frobJ]
  | succ j ih =>
    have h1 : frobJ F K (j + 1) x = frobJ F K j (FiniteField.frobeniusAlgHom F K x) := by
      simp only [frobJ, pow_succ, AlgHom.toLinearMap_apply, AlgHom.mul_apply]
    rw [h1, ih, FiniteField.frobeniusAlgHom_apply, ← pow_mul]
    congr 1
    ring

/-- A linearised polynomial `∑ aⱼ x^{q^j}` as an `F`-linear map. -/
noncomputable def qpoly {k : ℕ} (a : Fin (k + 1) → K) : K →ₗ[F] K :=
  ∑ j : Fin (k + 1), LinearMap.mulLeft F (a j) ∘ₗ frobJ F K j

theorem qpoly_apply {k : ℕ} (a : Fin (k + 1) → K) (x : K) :
    qpoly F K a x = ∑ j : Fin (k + 1), a j * x ^ (Fintype.card F ^ (j : ℕ)) := by
  simp [qpoly, LinearMap.sum_apply, frobJ_apply]

theorem root_bound {k : ℕ} (a : Fin (k + 1) → K) (ha : a ≠ 0) :
    finrank F (LinearMap.ker (qpoly F K a)) ≤ k := by
  classical
  have : FiniteDimensional F K := Module.Finite.of_finite
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    omega
  set p : K[X] := ∑ j : Fin (k + 1), C (a j) * X ^ (q ^ (j : ℕ)) with hp
  have hcoeff : ∀ j : Fin (k + 1), p.coeff (q ^ (j : ℕ)) = a j := by
    intro j
    rw [hp, finsetSum_coeff, Finset.sum_eq_single j]
    · simp [coeff_C_mul, coeff_X_pow]
    · intro i _ hij
      rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
      intro h
      apply hij
      exact Fin.ext (Nat.pow_right_injective hq2 h.symm)
    · simp
  have hp0 : p ≠ 0 := by
    intro h0
    apply ha
    funext j
    rw [← hcoeff j, h0, coeff_zero]
    rfl
  have hdeg : p.natDegree ≤ q ^ k := by
    rw [hp]
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have heval : ∀ x : K, p.eval x = qpoly F K a x := by
    intro x
    rw [qpoly_apply, hp, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hq]
  let Z : Finset K := Finset.univ.filter (fun x => qpoly F K a x = 0)
  have hZ : Z.val ⊆ p.roots := by
    intro x hx
    have hx' : x ∈ Z := hx
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    rw [mem_roots hp0, IsRoot, heval, hx']
  have hcard := card_le_degree_of_subset_roots hZ
  have hZc : Z.card = q ^ finrank F (LinearMap.ker (qpoly F K a)) := by
    have h1 : Nat.card (LinearMap.ker (qpoly F K a)) = Z.card := by
      rw [← Nat.card_eq_finsetCard]
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun x => by simp [Z, LinearMap.mem_ker])
    rw [← h1, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]
  have h2 : q ^ finrank F (LinearMap.ker (qpoly F K a)) ≤ q ^ k := by omega
  exact (Nat.pow_le_pow_iff_right (by omega)).mp h2

/-- the block map `y ↦ (y, y^q, …, y^{q^h})`. -/
noncomputable def blk (h : ℕ) : K →ₗ[F] (Fin (h + 1) → K) :=
  LinearMap.pi (fun j : Fin (h + 1) => frobJ F K j)

theorem blk_apply (h : ℕ) (y : K) (j : Fin (h + 1)) : blk F K h y j = frobJ F K j y := rfl

theorem blk_injective (h : ℕ) : Function.Injective (blk F K h) := by
  intro x y hxy
  have := congrFun hxy 0
  simpa [blk_apply, frobJ_apply] using this

theorem blk_P (h : ℕ) (S : Submodule K (Fin (h + 1) → K)) (hS : finrank K S ≤ h) :
    finrank F ↥(S.restrictScalars F ⊓ LinearMap.range (blk F K h)) ≤ finrank K S := by
  classical
  have : FiniteDimensional F K := Module.Finite.of_finite
  set k := finrank K S with hk
  have hkh : k + 1 ≤ h + 1 := by omega
  let g : S →ₗ[K] (Fin (k + 1) → K) :=
    (LinearMap.funLeft K K (Fin.castLE hkh)) ∘ₗ S.subtype
  have hlt : LinearMap.range g < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro htop
    have h1 := LinearMap.finrank_range_le g
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  let a : Fin (k + 1) → K := fun j => f (fun i => if j = i then 1 else 0)
  have hfa : ∀ w, f w = ∑ j, w j * a j := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    rfl
  have ha : a ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun w => ?_
    rw [hfa]
    simp [h0]
  have hle : Submodule.comap (blk F K h) (S.restrictScalars F) ≤
      LinearMap.ker (qpoly F K a) := by
    intro y hy
    have hyS : blk F K h y ∈ S := hy
    have hg : g ⟨_, hyS⟩ ∈ LinearMap.range g := LinearMap.mem_range_self g _
    have h1 := hfle hg
    rw [LinearMap.mem_ker, hfa] at h1
    rw [LinearMap.mem_ker, qpoly_apply, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [g, blk_apply, frobJ_apply, LinearMap.funLeft_apply, mul_comm]
  have heq : S.restrictScalars F ⊓ LinearMap.range (blk F K h) =
      Submodule.map (blk F K h) (Submodule.comap (blk F K h) (S.restrictScalars F)) := by
    rw [Submodule.map_comap_eq, inf_comm]
  rw [heq, ← (Submodule.equivMapOfInjective _ (blk_injective F K h) _).finrank_eq]
  exact (Submodule.finrank_mono hle).trans (root_bound F K a ha)

end frob

section glue

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]

theorem glue {V W : Type*} [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (h : ℕ) (π : V →ₗ[K] W) (U U0 : Submodule F V) (B : Submodule F W)
    (hker : ∀ v ∈ U, π v = 0 → v ∈ U0)
    (hmap : ∀ v ∈ U, π v ∈ B)
    (P0 : ∀ S : Submodule K V, finrank K S ≤ h →
      finrank F ↥(S.restrictScalars F ⊓ U0) ≤ finrank K S)
    (PB : ∀ S : Submodule K W, finrank K S ≤ h →
      finrank F ↥(S.restrictScalars F ⊓ B) ≤ finrank K S)
    (S : Submodule K V) (hS : finrank K S ≤ h) :
    finrank F ↥(S.restrictScalars F ⊓ U) ≤ finrank K S := by
  have : FiniteDimensional F K := Module.Finite.of_finite
  have : FiniteDimensional F V := Module.Finite.trans K V
  have : FiniteDimensional F W := Module.Finite.trans K W
  set T := S.restrictScalars F ⊓ U with hT
  let ρ : T →ₗ[F] W := (π.restrictScalars F) ∘ₗ T.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker ρ
  let σ : S →ₗ[K] W := π ∘ₗ S.subtype
  have hrnK := LinearMap.finrank_range_add_finrank_ker σ
  have hr1 : finrank F (LinearMap.range ρ) ≤ finrank K (LinearMap.range σ) := by
    refine le_trans (Submodule.finrank_mono ?_) (PB _ ((LinearMap.finrank_range_le σ).trans hS))
    rintro _ ⟨t, rfl⟩
    refine ⟨?_, hmap _ t.2.2⟩
    exact ⟨⟨t, t.2.1⟩, rfl⟩
  have hr2 : finrank F (LinearMap.ker ρ) ≤ finrank K (LinearMap.ker σ) := by
    have e1 : finrank F (LinearMap.ker ρ) = finrank F ((LinearMap.ker ρ).map T.subtype) :=
      (Submodule.equivMapOfInjective _ T.injective_subtype _).finrank_eq
    have e2 : finrank K (LinearMap.ker σ) = finrank K ((LinearMap.ker σ).map S.subtype) :=
      (Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq
    rw [e1, e2]
    refine le_trans (Submodule.finrank_mono ?_) (P0 _ ?_)
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : π t = 0 := ht
      exact ⟨⟨⟨t, t.2.1⟩, ht', rfl⟩, hker _ t.2.2 ht'⟩
    · rw [← e2]
      exact (Submodule.finrank_le _).trans hS
  omega

end glue

section main

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [FiniteDimensional K V]

/-- the construction `x ↦ ∑ᵢ ∑ⱼ xᵢ^{q^j} b(i,j)`. -/
noncomputable def psi {m h : ℕ} (b : Basis (Fin m × Fin (h + 1)) K V) :
    (Fin m → K) →ₗ[F] V where
  toFun x := ∑ p, frobJ F K p.2 (x p.1) • b p
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_assoc]

theorem equivFun_psi {m h : ℕ} (b : Basis (Fin m × Fin (h + 1)) K V) (x : Fin m → K) :
    b.equivFun (psi F K b x) = fun p => frobJ F K p.2 (x p.1) := by
  have : psi F K b x = b.equivFun.symm (fun p => frobJ F K p.2 (x p.1)) := by
    rw [Basis.equivFun_symm_apply]
    rfl
  rw [this]
  exact b.equivFun.apply_symm_apply _

theorem repr_psi {m h : ℕ} (b : Basis (Fin m × Fin (h + 1)) K V) (x : Fin m → K)
    (p : Fin m × Fin (h + 1)) : b.repr (psi F K b x) p = frobJ F K p.2 (x p.1) := by
  have := congrFun (equivFun_psi F K b x) p
  rwa [Basis.equivFun_apply] at this

/-- vectors supported on `s`. -/
def Zs {m : ℕ} (s : Finset (Fin m)) : Submodule F (Fin m → K) where
  carrier := {x | ∀ i, i ∉ s → x i = 0}
  add_mem' {x y} hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' i _ := rfl
  smul_mem' c x hx i hi := by simp [hx i hi]

theorem mem_Zs {m : ℕ} (s : Finset (Fin m)) (x : Fin m → K) :
    x ∈ Zs F K s ↔ ∀ i, i ∉ s → x i = 0 := Iff.rfl

theorem P_Us {m h : ℕ} (b : Basis (Fin m × Fin (h + 1)) K V) (s : Finset (Fin m)) :
    ∀ S : Submodule K V, finrank K S ≤ h →
      finrank F ↥(S.restrictScalars F ⊓ (Zs F K s).map (psi F K b)) ≤ finrank K S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro S _
    have hZ : Zs F K (∅ : Finset (Fin m)) = ⊥ := by
      ext x
      rw [mem_Zs, Submodule.mem_bot, funext_iff]
      simp
    rw [hZ, Submodule.map_bot, inf_bot_eq, finrank_bot]
    exact Nat.zero_le _
  | @insert i s hi ih =>
    intro S hS
    let π : V →ₗ[K] (Fin (h + 1) → K) :=
      LinearMap.funLeft K K (fun j => (i, j)) ∘ₗ b.equivFun.toLinearMap
    refine glue h π _ ((Zs F K s).map (psi F K b)) (LinearMap.range (blk F K h)) ?_ ?_ ih
      (blk_P F K h) S hS
    · rintro _ ⟨x, hx, rfl⟩ h0
      refine ⟨x, ?_, rfl⟩
      intro i' hi'
      by_cases hii : i' = i
      · subst hii
        have := congrFun h0 0
        simpa [π, repr_psi, frobJ_apply, LinearMap.funLeft_apply] using this
      · exact hx i' (by simp [hii, hi'])
    · rintro _ ⟨x, _, rfl⟩
      refine ⟨x i, ?_⟩
      funext j
      simp [π, repr_psi, blk_apply, LinearMap.funLeft_apply]

end main

open HScattered.Construction Module in
theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (hh : 0 < h) (hr : 0 < Module.finrank K V)
    (hdvd : (h + 1) ∣ Module.finrank K V) (hn : h + 1 ≤ Module.finrank F K) :
    ∃ U : Submodule F V, IsMaximumHScattered F K h U ∧
      (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K := by
  classical
  obtain ⟨m, hm⟩ := hdvd
  have : FiniteDimensional F K := Module.Finite.of_finite
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hcard : Fintype.card (Fin m × Fin (h + 1)) = finrank K V := by
    simp [hm, mul_comm]
  let b : Basis (Fin m × Fin (h + 1)) K V :=
    (Module.finBasis K V).reindex (Fintype.equivFinOfCardEq hcard).symm
  set U := LinearMap.range (psi F K b) with hUdef
  have hinj : Function.Injective (psi F K b) := by
    intro x y hxy
    funext i
    have := congrFun (congrArg b.equivFun hxy) (i, 0)
    simpa [repr_psi, frobJ_apply] using this
  have hdimU : finrank F U = m * finrank F K := by
    rw [hUdef, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    simp
  have hP : ∀ S : Submodule K V, finrank K S ≤ h →
      finrank F ↥(S.restrictScalars F ⊓ U) ≤ finrank K S := by
    intro S hS
    have h1 := P_Us F K b Finset.univ S hS
    have hZ : Zs F K (Finset.univ : Finset (Fin m)) = ⊤ := by
      ext x
      simp [mem_Zs]
    rwa [hZ, Submodule.map_top] at h1
  have hspan : Submodule.span K (U : Set V) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hex : ∃ p, f (b p) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf0 (b.ext fun p => by simp [hall p])
    obtain ⟨⟨i, j0⟩, hj0⟩ := hex
    let a : Fin (h + 1) → K := fun j => f (b (i, j))
    have ha : a ≠ 0 := fun h0 => hj0 (congrFun h0 j0)
    have hker : LinearMap.ker (qpoly F K a) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [LinearMap.mem_ker, qpoly_apply]
      have hmem : psi F K b (Pi.single i y) ∈ Submodule.span K (U : Set V) :=
        Submodule.subset_span ⟨_, rfl⟩
      have h1 := hfle hmem
      rw [LinearMap.mem_ker] at h1
      rw [← h1]
      simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp [a, frobJ_apply, mul_comm]
      · intro i' _ hi'
        simp [hi']
      · simp
    have h2 := root_bound F K a ha
    rw [hker, finrank_top] at h2
    omega
  refine ⟨U, ⟨⟨hh, ?_, hspan, fun S hS => ?_⟩, fun U' hU' => ?_⟩, ?_⟩
  · rw [hm]
    nlinarith
  · have := hP S hS.le
    omega
  · have h1 := bound h U' hU' hn
    rw [hdimU]
    have h2 : (h + 1) * finrank F U' ≤ (h + 1) * (m * finrank F K) := by
      rw [hm] at h1
      calc (h + 1) * finrank F U' ≤ (h + 1) * m * finrank F K := h1
        _ = (h + 1) * (m * finrank F K) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  · rw [hdimU, hm]
    ring
