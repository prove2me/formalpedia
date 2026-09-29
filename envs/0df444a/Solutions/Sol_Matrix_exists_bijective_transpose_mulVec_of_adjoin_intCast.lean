-- Prove2me | solution 1 for Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c2741d78-7356-5d37-829f-c8a6dd3392eb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace TrFrob

open Module

section Socle

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

def soc (χ : A →ₐ[k] k) : Submodule k A where
  carrier := {x | ∀ a : A, a * x = χ a • x}
  add_mem' {x y} hx hy a := by rw [mul_add, hx a, hy a, smul_add]
  zero_mem' a := by simp
  smul_mem' t {x} hx a := by rw [mul_smul_comm, hx a, smul_comm]

theorem mem_soc {χ : A →ₐ[k] k} {x : A} : x ∈ soc χ ↔ ∀ a : A, a * x = χ a • x := Iff.rfl

variable [FiniteDimensional k A]

theorem exists_char_of_forall_scalar (J : Ideal A) {x : A} (hxJ : x ∈ J) (hx : x ≠ 0)
    (h : ∀ b : A, ∃ μ : k, ∀ y ∈ J, b * y = μ • y) :
    ∃ χ : A →ₐ[k] k, x ∈ soc χ := by
  choose μ hμ using h
  have hinj : Function.Injective fun c : k => c • x := smul_left_injective k hx
  have hμx : ∀ b, b * x = μ b • x := fun b => hμ b x hxJ
  have h1 : μ 1 = 1 := hinj (by simp only; rw [← hμx 1, one_mul, one_smul])
  have hmul : ∀ b c, μ (b * c) = μ b * μ c := fun b c => hinj (by
    simp only
    rw [← hμx, mul_assoc, hμx c, mul_smul_comm, hμx b, smul_smul, mul_comm])
  have hadd : ∀ b c, μ (b + c) = μ b + μ c := fun b c => hinj (by
    simp only
    rw [← hμx, add_mul, hμx, hμx, add_smul])
  have h0 : μ 0 = 0 := hinj (by simp only; rw [← hμx 0, zero_mul, zero_smul])
  have hcomm : ∀ r : k, μ (algebraMap k A r) = r := fun r => hinj (by
    simp only
    rw [← hμx, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul])
  refine ⟨{ toFun := μ, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd,
            commutes' := hcomm }, fun a => ?_⟩
  exact hμx a

theorem exists_mem_soc_of_ne_bot [IsAlgClosed k] :
    ∀ (m : ℕ) (J : Ideal A), J ≠ ⊥ → finrank k (J.restrictScalars k) ≤ m →
      ∃ x ∈ J, x ≠ 0 ∧ ∃ χ : A →ₐ[k] k, x ∈ soc χ := by
  intro m
  induction m with
  | zero =>
    intro J hJ hm
    exfalso
    apply hJ
    have h0 : J.restrictScalars k = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hm)
    exact (Submodule.restrictScalars_eq_bot_iff _ _ _).mp h0
  | succ m ih =>
    intro J hJ hm
    by_cases h : ∀ b : A, ∃ μ : k, ∀ y ∈ J, b * y = μ • y
    · obtain ⟨x, hxJ, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
      exact ⟨x, hxJ, hx, exists_char_of_forall_scalar J hxJ hx h⟩
    · push Not at h
      obtain ⟨b, hb⟩ := h

      set Jk : Submodule k A := J.restrictScalars k with hJk
      have hJk_ne : Jk ≠ ⊥ := by
        intro h0
        exact hJ ((Submodule.restrictScalars_eq_bot_iff _ _ _).mp h0)
      haveI : Nontrivial Jk := Submodule.nontrivial_iff_ne_bot.mpr hJk_ne
      let L : Module.End k Jk :=
        { toFun := fun y => ⟨b * (y : A), J.mul_mem_left b y.2⟩
          map_add' := fun y z => by ext; simp [mul_add]
          map_smul' := fun t y => by ext; simp }
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue L
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      have hvL : b * (v : A) = μ • (v : A) := by
        have := hv.apply_eq_smul
        exact congrArg Subtype.val this
      have hv0 : (v : A) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)

      let J' : Ideal A :=
        { carrier := {y | y ∈ J ∧ b * y = μ • y}
          add_mem' := fun {y z} hy hz => ⟨J.add_mem hy.1 hz.1, by
            rw [mul_add, hy.2, hz.2, smul_add]⟩
          zero_mem' := ⟨J.zero_mem, by simp⟩
          smul_mem' := fun c {y} hy => ⟨J.mul_mem_left c hy.1, by
            rw [smul_eq_mul, mul_left_comm, hy.2, mul_smul_comm]⟩ }
      have hJ'le : J' ≤ J := fun y hy => hy.1
      have hJ'ne : J' ≠ ⊥ := by
        intro h0
        have : (v : A) ∈ J' := ⟨v.2, hvL⟩
        rw [h0] at this
        exact hv0 ((Submodule.mem_bot A).mp this)
      have hlt : J'.restrictScalars k < Jk := by
        refine lt_of_le_of_ne (fun y hy => hJ'le hy) ?_
        intro heq
        obtain ⟨y, hyJ, hy⟩ := hb μ
        have : y ∈ J'.restrictScalars k := by rw [heq]; exact hyJ
        exact hy this.2
      have hfin : finrank k (J'.restrictScalars k) ≤ m := by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨x, hxJ', hx, χ, hχ⟩ := ih J' hJ'ne hfin
      exact ⟨x, hJ'le hxJ', hx, χ, hχ⟩

theorem exists_frobeniusForm [IsAlgClosed k]
    (hsoc : ∀ (χ : A →ₐ[k] k) (x y : A), x ∈ soc χ → y ∈ soc χ → x ≠ 0 → ∃ t : k, y = t • x) :
    ∃ lam : Module.Dual k A, ∀ a : A, (∀ y, lam (a * y) = 0) → a = 0 := by

  let ι := {χ : A →ₐ[k] k // soc χ ≠ ⊥}
  haveI : Finite ι := Subtype.finite
  have hs : ∀ χ : ι, ∃ s : A, s ∈ soc χ.1 ∧ s ≠ 0 := fun χ =>
    Submodule.exists_mem_ne_zero_of_ne_bot χ.2
  choose s hs_mem hs_ne using hs

  have hex : ∀ χ : ι, ∃ lam : Module.Dual k A, Module.Dual.eval k A (s χ) lam ≠ 0 := by
    intro χ
    by_contra h
    push Not at h
    apply hs_ne χ
    exact (Module.forall_dual_apply_eq_zero_iff k (s χ)).mp h
  obtain ⟨lam, hlam⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists _ hex
  refine ⟨lam, fun a ha => ?_⟩
  by_contra ha0
  have hJ : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact ha0
  obtain ⟨x, hxJ, hx, χ, hχ⟩ :=
    exists_mem_soc_of_ne_bot (finrank k ((Ideal.span {a}).restrictScalars k)) (Ideal.span {a}) hJ le_rfl
  have hχne : soc χ ≠ ⊥ := by
    intro h0; rw [h0] at hχ; exact hx ((Submodule.mem_bot k).mp hχ)
  obtain ⟨t, ht⟩ := hsoc χ (s ⟨χ, hχne⟩) x (hs_mem ⟨χ, hχne⟩) hχ (hs_ne ⟨χ, hχne⟩)
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hxJ
  have h1 : lam (y * a) = 0 := by rw [mul_comm]; exact ha y
  have ht0 : t ≠ 0 := by
    rintro rfl; rw [zero_smul] at ht; exact hx ht
  apply hlam ⟨χ, hχne⟩
  have : lam (y * a) = t • lam (s ⟨χ, hχne⟩) := by rw [ht, map_smul]
  rw [h1] at this
  simpa [ht0] using this.symm

end Socle

open Matrix

section MatrixForm

variable {k : Type*} [Field k] {n d : ℕ}
variable (𝒜 : Subalgebra k (Matrix (Fin n) (Fin n) k))

def colMap (v : Fin d → (Fin n → k)) : (Fin d → 𝒜) →ₗ[k] (Fin n → k) where
  toFun c := ∑ j, (c j : Matrix (Fin n) (Fin n) k) *ᵥ v j
  map_add' c c' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.add_mulVec, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.smul_mulVec, RingHom.id_apply,
      Finset.smul_sum]

theorem colMap_apply (v : Fin d → (Fin n → k)) (c : Fin d → 𝒜) :
    colMap 𝒜 v c = ∑ j, (c j : Matrix (Fin n) (Fin n) k) *ᵥ v j := rfl

theorem colMap_mul (v : Fin d → (Fin n → k)) (a : 𝒜) (c : Fin d → 𝒜) :
    colMap 𝒜 v (fun j => a * c j) = (a : Matrix (Fin n) (Fin n) k) *ᵥ colMap 𝒜 v c := by
  simp only [colMap_apply, Subalgebra.coe_mul, Matrix.mulVec_sum, Matrix.mulVec_mulVec]

def rowMap (w : Fin d → (Fin n → k)) : (Fin d → 𝒜) →ₗ[k] (Fin n → k) where
  toFun c := ∑ j, ((c j : Matrix (Fin n) (Fin n) k))ᵀ *ᵥ w j
  map_add' c c' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.transpose_add, Matrix.add_mulVec,
      Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.transpose_smul, Matrix.smul_mulVec,
      RingHom.id_apply, Finset.smul_sum]

theorem rowMap_apply (w : Fin d → (Fin n → k)) (c : Fin d → 𝒜) :
    rowMap 𝒜 w c = ∑ j, ((c j : Matrix (Fin n) (Fin n) k))ᵀ *ᵥ w j := rfl

variable [IsMulCommutative 𝒜]

open scoped IsMulCommutative

variable {𝒜}
variable {v : Fin d → (Fin n → k)} (hv : Function.Bijective (colMap 𝒜 v))

def colEquiv : (Fin d → 𝒜) ≃ₗ[k] (Fin n → k) := LinearEquiv.ofBijective (colMap 𝒜 v) hv

theorem colEquiv_apply (c : Fin d → 𝒜) : colEquiv hv c = colMap 𝒜 v c := rfl

theorem colEquiv_mul (a : 𝒜) (c : Fin d → 𝒜) :
    colEquiv hv (fun j => a * c j) = (a : Matrix (Fin n) (Fin n) k) *ᵥ colEquiv hv c :=
  colMap_mul 𝒜 v a c

theorem mulVec_colEquiv_symm (a : 𝒜) (z : Fin n → k) :
    (colEquiv hv).symm ((a : Matrix (Fin n) (Fin n) k) *ᵥ z) = fun j => a * (colEquiv hv).symm z j := by
  apply (colEquiv hv).injective
  rw [LinearEquiv.apply_symm_apply, colEquiv_mul, LinearEquiv.apply_symm_apply]

include hv in
private theorem _root_.TrFrob.finrank_eq : finrank k (Fin d → 𝒜) = finrank k (Fin n → k) :=
  (colEquiv hv).finrank_eq

p2m_export "TrFrob" "finrank_eq"

def eigenEquiv (χ : 𝒜 →ₐ[k] k) :
    ↥(⨅ a : 𝒜, Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) k)) (χ a)) ≃ₗ[k]
      (Fin d → ↥(soc χ)) where
  toFun z := fun j => ⟨(colEquiv hv).symm (z : Fin n → k) j, by
    intro a
    have hz := (Submodule.mem_iInf _).mp z.2 a
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hz
    have h1 := congrFun (mulVec_colEquiv_symm hv a (z : Fin n → k)) j
    rw [hz, map_smul] at h1
    exact h1.symm⟩
  invFun c := ⟨colEquiv hv (fun j => (c j : 𝒜)), by
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, ← colEquiv_mul, ← map_smul]
    congr 1
    funext j
    exact (c j).2 a⟩
  map_add' z z' := by
    funext j; apply Subtype.ext
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' t z := by
    funext j; apply Subtype.ext
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, SetLike.val_smul]
  left_inv z := by
    apply Subtype.ext
    simp only [LinearEquiv.apply_symm_apply]
  right_inv c := by
    funext j; apply Subtype.ext
    simp only [LinearEquiv.symm_apply_apply]

include hv in

theorem soc_line (hd : 0 < d)
    (hmult : ∀ χ : 𝒜 →ₐ[k] k,
      finrank k ↥(⨅ a : 𝒜, Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) k))
        (χ a)) = d)
    (χ : 𝒜 →ₐ[k] k) (x y : 𝒜) (hx : x ∈ soc χ) (hy : y ∈ soc χ) (hx0 : x ≠ 0) :
    ∃ t : k, y = t • x := by
  haveI : Module.Free k ↥(soc χ) := Module.Free.of_divisionRing k ↥(soc χ)
  have h1 : finrank k ↥(soc χ) = 1 := by
    have h := hmult χ
    rw [(eigenEquiv hv χ).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h
    have : d * finrank k ↥(soc χ) = d * 1 := by rw [mul_one]; exact h
    exact Nat.eq_of_mul_eq_mul_left hd this
  obtain ⟨s, hs0, hs⟩ := (finrank_eq_one_iff' (K := k) (V := ↥(soc χ))).mp h1
  obtain ⟨cx, hcx⟩ := hs ⟨x, hx⟩
  obtain ⟨cy, hcy⟩ := hs ⟨y, hy⟩
  have hcx0 : cx ≠ 0 := by
    rintro rfl
    apply hx0
    have := congrArg Subtype.val hcx
    simpa using this.symm
  refine ⟨cy / cx, ?_⟩
  have ex : (x : 𝒜) = cx • (s : 𝒜) := by
    have := congrArg Subtype.val hcx; simpa using this.symm
  have ey : (y : 𝒜) = cy • (s : 𝒜) := by
    have := congrArg Subtype.val hcy; simpa using this.symm
  rw [ex, ey, smul_smul, div_mul_cancel₀ _ hcx0]

include hv in

theorem rowMap_injective (lam : Module.Dual k 𝒜)
    (hlam : ∀ a : 𝒜, (∀ y, lam (a * y) = 0) → a = 0) :
    ∃ w : Fin d → (Fin n → k), Function.Injective (rowMap 𝒜 w) := by
  classical

  let f : Fin d → Module.Dual k (Fin n → k) := fun j =>
    lam ∘ₗ (LinearMap.proj j : (Fin d → 𝒜) →ₗ[k] 𝒜) ∘ₗ ((colEquiv hv).symm : (Fin n → k) →ₗ[k] _)
  have hf : ∀ j z, f j z = lam ((colEquiv hv).symm z j) := fun j z => rfl
  let w : Fin d → (Fin n → k) := fun j i => f j (fun i' => if i = i' then 1 else 0)
  have hfw : ∀ j z, f j z = w j ⬝ᵥ z := by
    intro j z
    rw [LinearMap.pi_apply_eq_sum_univ (f j) z, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  refine ⟨w, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc

  have key : ∀ z : Fin n → k, ∑ j, f j ((c j : Matrix (Fin n) (Fin n) k) *ᵥ z) = 0 := by
    intro z
    have h0 : z ⬝ᵥ rowMap 𝒜 w c = 0 := by rw [hc, dotProduct_zero]
    rw [rowMap_apply, dotProduct_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_mulVec, vecMul_transpose, hfw, dotProduct_comm]
  funext j
  apply hlam
  intro y
  have hz := key (colEquiv hv (Pi.single j y))
  have hcalc : ∀ j', f j' ((c j' : Matrix (Fin n) (Fin n) k) *ᵥ colEquiv hv (Pi.single j y)) =
      lam (if j' = j then c j * y else 0) := by
    intro j'
    rw [hf, mulVec_colEquiv_symm, LinearEquiv.symm_apply_apply]
    congr 1
    by_cases h : j' = j
    · subst h; simp
    · simp [h]
  simp only [hcalc] at hz
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)] at hz
  simpa using hz

include hv in

theorem exists_bijective_rowMap [IsAlgClosed k]
    (hmult : ∀ χ : 𝒜 →ₐ[k] k,
      finrank k ↥(⨅ a : 𝒜, Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) k))
        (χ a)) = d) :
    ∃ w : Fin d → (Fin n → k), Function.Bijective (rowMap 𝒜 w) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·
    refine ⟨fun j => Fin.elim0 j, ?_⟩
    haveI : Subsingleton (Fin n → k) := ⟨fun a b => by
      obtain ⟨ca, rfl⟩ := hv.2 a
      obtain ⟨cb, rfl⟩ := hv.2 b
      rw [Subsingleton.elim ca cb]⟩
    exact ⟨fun a b _ => Subsingleton.elim _ _, fun z => ⟨fun j => Fin.elim0 j, Subsingleton.elim _ _⟩⟩
  · haveI : FiniteDimensional k 𝒜 :=
      FiniteDimensional.of_injective (𝒜.val.toLinearMap) Subtype.val_injective
    obtain ⟨lam, hlam⟩ := exists_frobeniusForm (k := k) (A := 𝒜) (soc_line hv hd hmult)
    obtain ⟨w, hw⟩ := rowMap_injective hv lam hlam
    refine ⟨w, ?_⟩
    have hdim : finrank k (Fin d → 𝒜) = finrank k (Fin n → k) := finrank_eq hv
    exact ⟨hw, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hw⟩

end MatrixForm

end TrFrob

namespace TrDesc

open Module Matrix

variable {ι : Type*} {n d : ℕ} (N : ι → Matrix (Fin n) (Fin n) ℤ)

def NK (K : Type*) [CommRing K] (i : ι) : Matrix (Fin n) (Fin n) K := (N i).map (Int.cast : ℤ → K)

theorem NK_apply (K : Type*) [CommRing K] (i : ι) : NK N K i = (N i).map (Int.cast : ℤ → K) := rfl

abbrev AK (K : Type*) [CommRing K] : Subalgebra K (Matrix (Fin n) (Fin n) K) :=
  Algebra.adjoin K (Set.range (NK N K))

theorem NK_map (K : Type*) [Field K] [CharZero K] (i : ι) :
    (NK N ℚ i).map (algebraMap ℚ K) = NK N K i := by
  rw [NK_apply, NK_apply, Matrix.map_map]
  congr 1
  funext z
  simp

def Tℚ : Submodule ℚ (Matrix (Fin n) (Fin n) ℚ) := Subalgebra.toSubmodule (AK N ℚ)

def g : ℕ := finrank ℚ (Tℚ N)

def c : Basis (Fin (g N)) ℚ (Tℚ N) := Module.finBasis ℚ (Tℚ N)

def cK (K : Type*) [Field K] [CharZero K] (k : Fin (g N)) : Matrix (Fin n) (Fin n) K :=
  ((c N k : Tℚ N) : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K)

theorem smul_map_algebraMap (K : Type*) [Field K] [CharZero K] (q : ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (q • A).map (algebraMap ℚ K) = (q : K) • A.map (algebraMap ℚ K) := by
  ext i j; simp

theorem eq_sum_of_mem_Tℚ (x : Tℚ N) :
    (x : Matrix (Fin n) (Fin n) ℚ) =
      ∑ k, (c N).repr x k • ((c N k : Tℚ N) : Matrix (Fin n) (Fin n) ℚ) := by
  have h := congrArg (Submodule.subtype (Tℚ N)) ((c N).sum_repr x).symm
  rw [map_sum] at h
  simpa using h

theorem map_mem_span_cK (K : Type*) [Field K] [CharZero K] (x : Tℚ N) :
    (x : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K) ∈ Submodule.span K (Set.range (cK N K)) := by
  rw [eq_sum_of_mem_Tℚ N x]
  rw [show (∑ k, (c N).repr x k • ((c N k : Tℚ N) : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ K)
      = (algebraMap ℚ K).mapMatrix (∑ k, (c N).repr x k • ((c N k : Tℚ N) : Matrix (Fin n) (Fin n) ℚ))
      from rfl, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [RingHom.mapMatrix_apply, smul_map_algebraMap]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem exists_of_mem_closure (K : Type*) [Field K] [CharZero K] {x : Matrix (Fin n) (Fin n) K}
    (hx : x ∈ Submonoid.closure (Set.range (NK N K))) :
    ∃ y ∈ Submonoid.closure (Set.range (NK N ℚ)), y.map (algebraMap ℚ K) = x := by
  have himg : ((algebraMap ℚ K).mapMatrix : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) K) ''
      Set.range (NK N ℚ) = Set.range (NK N K) := by
    ext z
    simp only [Set.mem_image, Set.mem_range, RingHom.mapMatrix_apply]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (NK_map N K i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, NK_map N K i⟩
  have h := MonoidHom.map_mclosure
    ((algebraMap ℚ K).mapMatrix : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) K)
    (Set.range (NK N ℚ))
  rw [himg] at h
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := Submonoid.mem_map.mp hx
  exact ⟨y, hy, rfl⟩

theorem map_mem_closure (K : Type*) [Field K] [CharZero K] {y : Matrix (Fin n) (Fin n) ℚ}
    (hy : y ∈ Submonoid.closure (Set.range (NK N ℚ))) :
    y.map (algebraMap ℚ K) ∈ Submonoid.closure (Set.range (NK N K)) := by
  have himg : ((algebraMap ℚ K).mapMatrix : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) K) ''
      Set.range (NK N ℚ) = Set.range (NK N K) := by
    ext z
    simp only [Set.mem_image, Set.mem_range, RingHom.mapMatrix_apply]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (NK_map N K i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, NK_map N K i⟩
  have h := MonoidHom.map_mclosure
    ((algebraMap ℚ K).mapMatrix : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) K)
    (Set.range (NK N ℚ))
  rw [himg] at h
  rw [← h]
  exact Submonoid.mem_map.mpr ⟨y, hy, rfl⟩

theorem toSubmodule_AK_le (K : Type*) [Field K] [CharZero K] :
    Subalgebra.toSubmodule (AK N K) ≤ Submodule.span K (Set.range (cK N K)) := by
  rw [Algebra.adjoin_eq_span, Submodule.span_le]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_closure N K hx
  have hyT : y ∈ Tℚ N := by
    change y ∈ Subalgebra.toSubmodule (Algebra.adjoin ℚ (Set.range (NK N ℚ)))
    rw [Algebra.adjoin_eq_span]
    exact Submodule.subset_span hy
  exact map_mem_span_cK N K ⟨y, hyT⟩

theorem cK_mem_AK (K : Type*) [Field K] [CharZero K] (k : Fin (g N)) : cK N K k ∈ AK N K := by
  have hmem : ((c N k : Tℚ N) : Matrix (Fin n) (Fin n) ℚ) ∈ Tℚ N := (c N k).2
  change _ ∈ Subalgebra.toSubmodule (Algebra.adjoin ℚ (Set.range (NK N ℚ))) at hmem
  rw [Algebra.adjoin_eq_span] at hmem
  unfold cK
  refine Submodule.span_induction (p := fun x _ => x.map (algebraMap ℚ K) ∈ AK N K) ?_ ?_ ?_ ?_ hmem
  · intro y hy
    have h1 := map_mem_closure N K hy
    have h2 : (Submonoid.closure (Set.range (NK N K)) : Set (Matrix (Fin n) (Fin n) K)) ⊆ AK N K := by
      change Submonoid.closure (Set.range (NK N K)) ≤ (AK N K).toSubmonoid
      exact Submonoid.closure_le.mpr Algebra.subset_adjoin
    exact h2 h1
  · simp only [Matrix.map_zero, map_zero]; exact (AK N K).zero_mem
  · intro x y _ _ hx hy
    rw [Matrix.map_add _ (map_add (algebraMap ℚ K))]; exact (AK N K).add_mem hx hy
  · intro r x _ hx
    rw [smul_map_algebraMap]; exact (AK N K).smul_mem hx _

theorem finrank_AK_le (K : Type*) [Field K] [CharZero K] : finrank K (AK N K) ≤ g N := by
  calc finrank K (AK N K)
      = finrank K (Subalgebra.toSubmodule (AK N K)) := (Subalgebra.finrank_toSubmodule _).symm
    _ ≤ finrank K (Submodule.span K (Set.range (cK N K))) := Submodule.finrank_mono (toSubmodule_AK_le N K)
    _ ≤ Fintype.card (Fin (g N)) := finrank_range_le_card _
    _ = g N := Fintype.card_fin _

def flat (K : Type*) [CommRing K] : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K) where
  toFun A := fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flat_injective (K : Type*) [CommRing K] : Function.Injective (flat (n := n) K) := by
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem linearIndependent_of_rat (K : Type*) [Field K] [CharZero K] {κ : Type*}
    (v : κ → Matrix (Fin n) (Fin n) ℚ) (hv : LinearIndependent ℚ v) :
    LinearIndependent K (fun i => (v i).map (algebraMap ℚ K)) := by
  have h1 : LinearIndependent ℚ (fun i => flat ℚ (v i)) :=
    hv.map' (flat ℚ) (LinearMap.ker_eq_bot.mpr (flat_injective ℚ))
  have h2 : LinearIndependent K (fun i => (algebraMap ℚ K) ∘ (flat ℚ (v i))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := K)).mpr h1
  have h3 : (fun i => (algebraMap ℚ K) ∘ (flat ℚ (v i))) =
      fun i => flat K ((v i).map (algebraMap ℚ K)) := by
    funext i; funext ij; rfl
  rw [h3] at h2
  exact LinearIndependent.of_comp (flat K) h2

theorem linearIndependent_cK (K : Type*) [Field K] [CharZero K] : LinearIndependent K (cK N K) := by
  have h : LinearIndependent ℚ (fun k => ((c N k : Tℚ N) : Matrix (Fin n) (Fin n) ℚ)) :=
    (c N).linearIndependent.map' (Tℚ N).subtype (Submodule.ker_subtype _)
  exact linearIndependent_of_rat K _ h

theorem finrank_AK_eq (K : Type*) [Field K] [CharZero K] : finrank K (AK N K) = g N := by
  refine le_antisymm (finrank_AK_le N K) ?_
  have hli : LinearIndependent K (fun k : Fin (g N) => (⟨cK N K k, cK_mem_AK N K k⟩ : AK N K)) := by
    apply LinearIndependent.of_comp (AK N K).val.toLinearMap
    exact linearIndependent_cK N K
  haveI : Module.Finite K (AK N K) :=
    FiniteDimensional.of_injective (AK N K).val.toLinearMap Subtype.val_injective
  simpa using hli.fintype_card_le_finrank

def ψ (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K) :
    (Fin d → AK N K) →ₗ[K] (Fin n → K) where
  toFun s := ∑ a, ((s a : AK N K) : Matrix (Fin n) (Fin n) K) *ᵥ v a
  map_add' s s' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.add_mulVec, Finset.sum_add_distrib]
  map_smul' r s := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.smul_mulVec, RingHom.id_apply,
      Finset.smul_sum]

theorem ψ_apply (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K) (s : Fin d → AK N K) :
    ψ N K v s = ∑ a, ((s a : AK N K) : Matrix (Fin n) (Fin n) K) *ᵥ v a := rfl

section Square

variable (hn : d * g N = n)

def σ : Fin d × Fin (g N) ≃ Fin n :=
  Fintype.equivOfCardEq (by simp [hn])

def Φ (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (cK N K ((σ N hn).symm j).2 *ᵥ v ((σ N hn).symm j).1) i

theorem Φ_col (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K) (ak : Fin d × Fin (g N)) :
    (Φ N hn K v).col (σ N hn ak) = cK N K ak.2 *ᵥ v ak.1 := by
  funext i
  simp [Φ]

theorem Φ_map (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → ℚ) :
    (Φ N hn ℚ v).map (algebraMap ℚ K) = Φ N hn K (fun a => (algebraMap ℚ K) ∘ v a) := by
  ext i j
  simp only [Φ, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  simp only [cK, Matrix.map_map]
  congr 2

theorem span_cols_Φ_eq_top (K : Type*) [Field K] [CharZero K] (w : Fin d → Fin n → K)
    (hw : Submodule.span K (Set.range fun ua : AK N K × Fin d =>
      ((ua.1 : AK N K) : Matrix (Fin n) (Fin n) K) *ᵥ w ua.2) = ⊤) :
    Submodule.span K (Set.range (Φ N hn K w).col) = ⊤ := by
  apply top_le_iff.mp
  rw [← hw]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, a⟩, rfl⟩
  have hmem := toSubmodule_AK_le N K u.2
  simp only [SetLike.mem_coe]
  refine Submodule.span_induction
    (p := fun x _ => x *ᵥ w a ∈ Submodule.span K (Set.range (Φ N hn K w).col)) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨σ N hn (a, k), ?_⟩
    exact Φ_col N hn K w (a, k)
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ r hx

theorem isUnit_Φ (K : Type*) [Field K] [CharZero K] (w : Fin d → Fin n → K)
    (hw : Submodule.span K (Set.range fun ua : AK N K × Fin d =>
      ((ua.1 : AK N K) : Matrix (Fin n) (Fin n) K) *ᵥ w ua.2) = ⊤) :
    IsUnit (Φ N hn K w) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_cols_Φ_eq_top N hn K w hw).ge (by simp)

theorem span_cols_Φ_of_isUnit (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K)
    (hv : IsUnit (Φ N hn K v)) :
    Submodule.span K (Set.range (Φ N hn K v).col) = ⊤ := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit] at hv
  exact hv.span_eq_top_of_card_eq_finrank' (by simp)

def Φpoly : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d × Fin n) ℚ) :=
  Matrix.of fun i j => ∑ m, MvPolynomial.C
    (((c N ((σ N hn).symm j).2 : Tℚ N) : Matrix (Fin n) (Fin n) ℚ) i m) *
      MvPolynomial.X (((σ N hn).symm j).1, m)

theorem aeval_Φpoly (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K) :
    (MvPolynomial.aeval (fun am : Fin d × Fin n => v am.1 am.2) :
        MvPolynomial (Fin d × Fin n) ℚ →ₐ[ℚ] K).toRingHom.mapMatrix (Φpoly N hn) = Φ N hn K v := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Φpoly, Φ, Matrix.of_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Matrix.mulVec, dotProduct, cK]

theorem det_Φ_eq_aeval (K : Type*) [Field K] [CharZero K] (v : Fin d → Fin n → K) :
    (Φ N hn K v).det =
      MvPolynomial.aeval (fun am : Fin d × Fin n => v am.1 am.2) (Φpoly N hn).det := by
  rw [← aeval_Φpoly N hn K v]
  exact (RingHom.map_det _ _).symm

theorem exists_rat_isUnit_Φ (hw : ∃ w : Fin d → Fin n → ℂ, IsUnit (Φ N hn ℂ w)) :
    ∃ v : Fin d → Fin n → ℚ, IsUnit (Φ N hn ℚ v) := by
  obtain ⟨w, hw⟩ := hw
  by_contra hcon
  push Not at hcon
  have hP : (Φpoly N hn).det = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    have h1 := hcon (fun a m => x (a, m))
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, det_Φ_eq_aeval] at h1
    rw [← MvPolynomial.aeval_eq_eval]
    exact h1
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_Φ_eq_aeval, hP, map_zero] at hw
  exact hw rfl

end Square

section OverK

variable (K : Type*) [Field K] [CharZero K]
variable (hn : d * g N = n) (vq : Fin d → Fin n → ℚ)

def vK : Fin d → Fin n → K := fun a => (algebraMap ℚ K) ∘ vq a

theorem ψ_surjective (hv : IsUnit (Φ N hn ℚ vq)) : Function.Surjective (ψ N K (vK K vq)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hvp : IsUnit (Φ N hn K (vK K vq)) := by
    have := (RingHom.mapMatrix (algebraMap ℚ K)).isUnit_map hv
    rwa [RingHom.mapMatrix_apply, Φ_map] at this
  rw [← span_cols_Φ_of_isUnit N hn K (vK K vq) hvp, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨⟨a, k⟩, rfl⟩ := (σ N hn).surjective j
  rw [Φ_col]
  refine ⟨Pi.single a ⟨cK N K k, cK_mem_AK N K k⟩, ?_⟩
  rw [ψ_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

include hn in
theorem finrank_source_eq : finrank K (Fin d → AK N K) = n := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    finrank_AK_eq, hn]

theorem ψ_bijective (hv : IsUnit (Φ N hn ℚ vq)) : Function.Bijective (ψ N K (vK K vq)) := by
  have hsurj := ψ_surjective N K hn vq hv
  refine ⟨?_, hsurj⟩
  haveI : Module.Finite K (AK N K) :=
    FiniteDimensional.of_injective (AK N K).val.toLinearMap Subtype.val_injective
  have hdim : finrank K (Fin d → AK N K) = finrank K (Fin n → K) := by
    rw [finrank_source_eq N K hn, Module.finrank_fin_fun]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj

end OverK

theorem descent
    (hfree : ∃ w : Fin d → (Fin n → ℂ), Function.Bijective (ψ N ℂ w))
    (K : Type*) [Field K] [CharZero K] :
    ∃ w : Fin d → (Fin n → K), Function.Bijective (ψ N K w) := by
  obtain ⟨w, hw⟩ := hfree
  haveI : Module.Finite ℂ (AK N ℂ) :=
    FiniteDimensional.of_injective (AK N ℂ).val.toLinearMap Subtype.val_injective

  have hn : d * g N = n := by
    have h := (LinearEquiv.ofBijective (ψ N ℂ w) hw).finrank_eq
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      finrank_AK_eq, Module.finrank_fin_fun] at h
    exact h

  have hspan : Submodule.span ℂ (Set.range fun ua : AK N ℂ × Fin d =>
      ((ua.1 : AK N ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ w ua.2) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨s, rfl⟩ := hw.2 z
    rw [ψ_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨(s a, a), rfl⟩
  obtain ⟨vq, hvq⟩ := exists_rat_isUnit_Φ N hn ⟨w, isUnit_Φ N hn ℂ w hspan⟩
  exact ⟨vK K vq, ψ_bijective N K hn vq hvq⟩

end TrDesc

namespace TrFinal

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

theorem transpose_mem_adjoin {s : Set (Matrix (Fin n) (Fin n) R)} {a : Matrix (Fin n) (Fin n) R}
    (ha : a ∈ Algebra.adjoin R s) : aᵀ ∈ Algebra.adjoin R (Matrix.transpose '' s) := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | algebraMap r =>
    rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose, ← Matrix.algebraMap_eq_diagonal]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [Matrix.transpose_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [Matrix.transpose_mul]; exact mul_mem hy hx

variable {ι : Type*} (M : ι → Matrix (Fin n) (Fin n) ℤ)

theorem image_transpose_range (K : Type*) [CommRing K] :
    Matrix.transpose '' (Set.range fun i => (M i).map (Int.cast : ℤ → K)) =
      Set.range fun i => ((M i)ᵀ).map (Int.cast : ℤ → K) := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, Matrix.transpose_map⟩
  · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, Matrix.transpose_map.symm⟩

theorem image_transpose_range' (K : Type*) [CommRing K] :
    Matrix.transpose '' (Set.range fun i => ((M i)ᵀ).map (Int.cast : ℤ → K)) =
      Set.range fun i => (M i).map (Int.cast : ℤ → K) := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, by rw [Matrix.transpose_map, Matrix.transpose_transpose]⟩
  · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, by rw [Matrix.transpose_map, Matrix.transpose_transpose]⟩

def τ (K : Type*) [CommRing K] :
    ↥(Algebra.adjoin K (Set.range fun i => (M i).map (Int.cast : ℤ → K))) ≃
      ↥(Algebra.adjoin K (Set.range fun i => ((M i)ᵀ).map (Int.cast : ℤ → K))) where
  toFun a := ⟨(a : Matrix (Fin n) (Fin n) K)ᵀ, by
    have h := transpose_mem_adjoin a.2
    rwa [image_transpose_range] at h⟩
  invFun b := ⟨(b : Matrix (Fin n) (Fin n) K)ᵀ, by
    have h := transpose_mem_adjoin b.2
    rwa [image_transpose_range'] at h⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

theorem coe_τ_symm (K : Type*) [CommRing K]
    (b : ↥(Algebra.adjoin K (Set.range fun i => ((M i)ᵀ).map (Int.cast : ℤ → K)))) :
    (((τ M K).symm b : ↥(Algebra.adjoin K (Set.range fun i => (M i).map (Int.cast : ℤ → K)))) :
      Matrix (Fin n) (Fin n) K) = (b : Matrix (Fin n) (Fin n) K)ᵀ := rfl

end TrFinal

open TrFinal Matrix in
theorem solution
    {ι : Type*} (n d : ℕ) (M : ι → Matrix (Fin n) (Fin n) ℤ)
    (hcomm : ∀ i j, M i * M j = M j * M i)
    (hfree : ∃ v : Fin d → (Fin n → ℂ), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k))))
    (hmult : ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = d)
    (K : Type*) [Field K] [CharZero K] :
    ∃ w : Fin d → (Fin n → K), Function.Bijective
      (fun c : Fin d → ↥(Algebra.adjoin K (Set.range fun i => ((M i).transpose).map (Int.cast : ℤ → K))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) K).mulVec (w k))) := by

  set 𝒜 := Algebra.adjoin ℂ (Set.range fun i => (M i).map (Int.cast : ℤ → ℂ)) with h𝒜
  haveI : IsMulCommutative 𝒜 := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    change (Int.castRingHom ℂ).mapMatrix (M i) * (Int.castRingHom ℂ).mapMatrix (M j) =
      (Int.castRingHom ℂ).mapMatrix (M j) * (Int.castRingHom ℂ).mapMatrix (M i)
    rw [← map_mul, ← map_mul, hcomm])

  obtain ⟨v, hv⟩ := hfree
  have hv' : Function.Bijective (TrFrob.colMap 𝒜 v) := hv
  obtain ⟨w, hw⟩ := TrFrob.exists_bijective_rowMap hv' hmult

  let N : ι → Matrix (Fin n) (Fin n) ℤ := fun i => (M i)ᵀ
  have hfreeN : ∃ w : Fin d → (Fin n → ℂ), Function.Bijective (TrDesc.ψ N ℂ w) := by
    refine ⟨w, ?_⟩
    let e : (Fin d → ↥(Algebra.adjoin ℂ (Set.range fun i => ((M i)ᵀ).map (Int.cast : ℤ → ℂ)))) ≃
        (Fin d → 𝒜) := Equiv.arrowCongr (Equiv.refl _) (τ M ℂ).symm
    have hfac : (TrDesc.ψ N ℂ w : (Fin d → TrDesc.AK N ℂ) → (Fin n → ℂ)) =
        (TrFrob.rowMap 𝒜 w) ∘ e := by
      funext c'
      rw [TrDesc.ψ_apply, Function.comp_apply, TrFrob.rowMap_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = (((τ M ℂ).symm (c' j) : 𝒜) : Matrix (Fin n) (Fin n) ℂ)ᵀ *ᵥ w j
      rw [coe_τ_symm, Matrix.transpose_transpose]
    rw [hfac]
    exact hw.comp e.bijective

  obtain ⟨wK, hwK⟩ := TrDesc.descent N hfreeN K
  exact ⟨wK, hwK⟩

end

end S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast
end P2MW
export P2MW.S_Matrix_exists_bijective_transpose_mulVec_of_adjoin_intCast (solution)
