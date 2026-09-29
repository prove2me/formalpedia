-- Prove2me | solution 1 for MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/51a2e7cd-c494-5352-92db-421865b7175b

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le

set_option autoImplicit false

namespace GreenHRT

open MvPolynomial

section SemiCont

variable {K : Type} [Field K] {N : ℕ}
variable {E F : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

def fam (g : Fin N → E →ₗ[K] F) (a : Fin N → K) : E →ₗ[K] F := ∑ i, a i • g i

theorem fam_apply (g : Fin N → E →ₗ[K] F) (a : Fin N → K) (x : E) : fam g a x = ∑ i, a i • g i x := by
  simp [fam, LinearMap.sum_apply]

theorem exists_generic_rank [Module.Finite K E] (g : Fin N → E →ₗ[K] F) :
    ∃ G : MvPolynomial (Fin N) K, G ≠ 0 ∧ ∀ a : Fin N → K, eval a G ≠ 0 →
      ∀ a' : Fin N → K, Module.finrank K ↥(LinearMap.range (fam g a')) ≤
        Module.finrank K ↥(LinearMap.range (fam g a)) := by
  classical

  set B := Module.finrank K E with hB
  have hbound : ∀ a, Module.finrank K ↥(LinearMap.range (fam g a)) ≤ B := fun a =>
    LinearMap.finrank_range_le (fam g a)
  let P : ℕ → Prop := fun m => ∃ a, m ≤ Module.finrank K ↥(LinearMap.range (fam g a))
  have hP : P (Nat.findGreatest P B) := Nat.findGreatest_spec (P := P) (Nat.zero_le B) ⟨0, Nat.zero_le _⟩
  obtain ⟨a₀, ha₀⟩ := hP
  have hmax : ∀ a', Module.finrank K ↥(LinearMap.range (fam g a')) ≤ Nat.findGreatest P B := fun a' =>
    Nat.le_findGreatest (hbound a') ⟨a', le_rfl⟩

  set ρ := Module.finrank K ↥(LinearMap.range (fam g a₀)) with hρ
  let bR := Module.finBasis K ↥(LinearMap.range (fam g a₀))
  have hpre : ∀ i : Fin ρ, ∃ x : E, fam g a₀ x = (bR i : F) := fun i => LinearMap.mem_range.mp (bR i).2
  choose xs hxs using hpre
  let w : Fin ρ → F := fun i => (bR i : F)
  have hli : LinearIndependent K w :=
    bR.linearIndependent.map' (LinearMap.range (fam g a₀)).subtype (Submodule.ker_subtype _)

  let bW := Module.Basis.span hli
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend (bW.equivFun : ↥(Submodule.span K (Set.range w)) →ₗ[K] (Fin ρ → K))
  have hπw : ∀ i j : Fin ρ, π (w i) j = if i = j then 1 else 0 := by
    intro i j
    have hmem : w i ∈ Submodule.span K (Set.range w) := Submodule.subset_span ⟨i, rfl⟩
    have h1 : π (w i) = bW.equivFun ⟨w i, hmem⟩ := by
      have := LinearMap.congr_fun hπ ⟨w i, hmem⟩
      simpa using this
    have h2 : (⟨w i, hmem⟩ : ↥(Submodule.span K (Set.range w))) = bW i := by
      apply Subtype.ext; simp [bW, Module.Basis.span_apply]
    rw [h1, h2, Module.Basis.equivFun_self]

  let PM : Matrix (Fin ρ) (Fin ρ) (MvPolynomial (Fin N) K) :=
    Matrix.of fun i j => ∑ k : Fin N, C (π (g k (xs i)) j) * X k
  let Mx : (Fin N → K) → Matrix (Fin ρ) (Fin ρ) K := fun a => Matrix.of fun i j => π (fam g a (xs i)) j
  have hMx : ∀ a, (eval a).mapMatrix PM = Mx a := by
    intro a
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, PM, Mx, map_sum, map_mul, eval_C,
      MvPolynomial.eval_X, fam_apply, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdet : ∀ a, eval a PM.det = (Mx a).det := fun a => by rw [RingHom.map_det, hMx]
  have hMx₀ : Mx a₀ = 1 := by
    ext i j
    simp only [Mx, Matrix.of_apply, Matrix.one_apply]
    rw [hxs i]
    exact hπw i j
  refine ⟨PM.det, ?_, ?_⟩
  · intro h
    have := hdet a₀
    rw [h, map_zero, hMx₀, Matrix.det_one] at this
    exact zero_ne_one this
  · intro a ha a'
    rw [hdet a] at ha

    have hrows : LinearIndependent K (fun i => Mx a i) := Matrix.linearIndependent_rows_of_det_ne_zero ha
    have hrows' : LinearIndependent K (π ∘ fun i => fam g a (xs i)) := by
      convert hrows using 1
      funext i
      ext j
      simp [Mx]
    have hli' : LinearIndependent K (fun i => fam g a (xs i)) := LinearIndependent.of_comp π hrows'
    let v' : Fin ρ → ↥(LinearMap.range (fam g a)) := fun i => ⟨fam g a (xs i), LinearMap.mem_range_self _ _⟩
    have hv' : LinearIndependent K v' := by
      apply LinearIndependent.of_comp (LinearMap.range (fam g a)).subtype
      exact hli'
    have hcard := hv'.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    exact (hmax a').trans (ha₀.trans hcard)

end SemiCont

section Pieces

variable (K : Type) [Field K] (M : ℕ)

abbrev HS (m : ℕ) : Submodule K (MvPolynomial (Fin M) K) := homogeneousSubmodule (Fin M) K m

scoped instance finite_HS (m : ℕ) : Module.Finite K ↥(HS K M m) := by
  rw [HS, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin M →₀ ℕ | x.degree = m} :=
    ((Finsupp.finite_of_degree_le m).subset fun x (hx : x.degree = m) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K {x : Fin M →₀ ℕ | x.degree = m})

variable {K M}

noncomputable def lin (a : Fin M → K) : MvPolynomial (Fin M) K := ∑ i, C (a i) * X i

theorem lin_isHomogeneous (a : Fin M → K) : (lin a).IsHomogeneous 1 := by
  unfold lin
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _

theorem lin_mem (a : Fin M → K) : lin a ∈ HS K M 1 := lin_isHomogeneous a

theorem coeff_lin_single (a : Fin M → K) (i : Fin M) : coeff (Finsupp.single i 1) (lin a) = a i := by
  classical
  unfold lin
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X', mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg]
    intro h
    exact hji (Finsupp.single_left_injective one_ne_zero h)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem lin_ne_zero {a : Fin M → K} {i : Fin M} (h : a i ≠ 0) : lin a ≠ 0 := by
  intro h0
  have := coeff_lin_single a i
  rw [h0, coeff_zero] at this
  exact h this.symm

theorem lin_zero : lin (0 : Fin M → K) = 0 := by simp [lin]

theorem lin_add (a b : Fin M → K) : lin (a + b) = lin a + lin b := by
  simp [lin, Finset.sum_add_distrib, add_mul]

theorem lin_smul (c : K) (a : Fin M → K) : lin (c • a) = C c * lin a := by
  simp [lin, Finset.mul_sum, mul_assoc]

theorem lin_single [DecidableEq (Fin M)] (i : Fin M) : lin (Pi.single i (1 : K)) = X i := by
  unfold lin
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem exists_eq_single_of_degree_eq_one (s : Fin M →₀ ℕ) (hs : s.degree = 1) :
    ∃ i, s = Finsupp.single i 1 := by
  classical
  have hne : s ≠ 0 := by rintro rfl; simp at hs
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hi1 : 1 ≤ s i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  refine ⟨i, ?_⟩
  have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.mpr hi1
  obtain ⟨t, ht⟩ := exists_add_of_le hle
  have hdeg : t.degree = 0 := by
    have := congrArg Finsupp.degree ht
    rw [map_add, Finsupp.degree_single, hs] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hdeg
  rw [ht, hdeg, add_zero]

theorem eq_lin_of_mem_one {p : MvPolynomial (Fin M) K} (hp : p ∈ HS K M 1) :
    p = lin (fun i => coeff (Finsupp.single i 1) p) := by
  classical
  ext s
  by_cases hs : s.degree = 1
  · obtain ⟨i, rfl⟩ := exists_eq_single_of_degree_eq_one s hs
    rw [coeff_lin_single]
  · have h1 : coeff s p = 0 := by
      by_contra h
      exact hs (by simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using hp h)
    have h2 : coeff s (lin fun i => coeff (Finsupp.single i 1) p) = 0 := by
      by_contra h
      exact hs (by simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using lin_isHomogeneous _ h)
    rw [h1, h2]

noncomputable def mulSub (ℓ : MvPolynomial (Fin M) K) (m : ℕ) : Submodule K (MvPolynomial (Fin M) K) :=
  (HS K M m).map (LinearMap.mulLeft K ℓ)

theorem mul_mem_mulSub (ℓ : MvPolynomial (Fin M) K) {m : ℕ} {p : MvPolynomial (Fin M) K} (hp : p ∈ HS K M m) :
    ℓ * p ∈ mulSub ℓ m := Submodule.mem_map_of_mem hp

theorem mem_mulSub_iff (ℓ : MvPolynomial (Fin M) K) (m : ℕ) (q : MvPolynomial (Fin M) K) :
    q ∈ mulSub ℓ m ↔ ∃ p ∈ HS K M m, ℓ * p = q := Submodule.mem_map

theorem mulSub_le {ℓ : MvPolynomial (Fin M) K} (hℓ : ℓ ∈ HS K M 1) (m : ℕ) : mulSub ℓ m ≤ HS K M (m + 1) := by
  rintro _ ⟨p, hp, rfl⟩
  show (ℓ * p).IsHomogeneous (m + 1)
  rw [Nat.add_comm]; exact IsHomogeneous.mul hℓ hp

theorem finrank_mulSub {ℓ : MvPolynomial (Fin M) K} (hℓ : ℓ ≠ 0) (m : ℕ) :
    Module.finrank K ↥(mulSub ℓ m) = Module.finrank K ↥(HS K M m) := by
  have hinj : Function.Injective (LinearMap.mulLeft K ℓ) := fun p q h => mul_left_cancel₀ hℓ h
  exact ((Submodule.equivMapOfInjective _ hinj (HS K M m)).finrank_eq).symm

theorem mulSub_zero (m : ℕ) : mulSub (0 : MvPolynomial (Fin M) K) m = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨p, _, rfl⟩
  simp

scoped instance finite_mulSub (ℓ : MvPolynomial (Fin M) K) (m : ℕ) : Module.Finite K ↥(mulSub ℓ m) :=
  Module.Finite.map _ _

noncomputable def codim (K : Type) [Field K] (M m : ℕ) (V : Submodule K (MvPolynomial (Fin M) K)) : ℕ :=
  Module.finrank K ↥(HS K M m) - Module.finrank K ↥V

theorem finrank_le_of_le {m : ℕ} {V : Submodule K (MvPolynomial (Fin M) K)} (hV : V ≤ HS K M m) :
    Module.finrank K ↥V ≤ Module.finrank K ↥(HS K M m) := Submodule.finrank_mono hV

theorem finrank_map_add {X' : Type*} [AddCommGroup X'] [Module K X']
    (f : MvPolynomial (Fin M) K →ₗ[K] X') (p W : Submodule K (MvPolynomial (Fin M) K)) [Module.Finite K ↥p]
    (hW : W ≤ p) (hker : ∀ x ∈ p, f x = 0 ↔ x ∈ W) :
    Module.finrank K ↥(p.map f) + Module.finrank K ↥W = Module.finrank K ↥p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have hk : (LinearMap.ker f).comap p.subtype = W.comap p.subtype := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker]
    exact hker x hx
  rw [hk, (Submodule.comapSubtypeEquivOfLe hW).finrank_eq] at h
  exact h

theorem finrank_sup_eq (V A : Submodule K (MvPolynomial (Fin M) K)) [Module.Finite K ↥V] [Module.Finite K ↥A] :
    Module.finrank K ↥(V ⊔ A) = Module.finrank K ↥V + Module.finrank K ↥(A.map V.mkQ) := by
  have h := finrank_map_add V.mkQ (V ⊔ A) V le_sup_left (fun x _ => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero])
  rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq] at h
  omega

theorem finrank_sup_mulSub_add {m : ℕ} (V : Submodule K (MvPolynomial (Fin M) K)) [Module.Finite K ↥V]
    (ℓ : MvPolynomial (Fin M) K) :
    Module.finrank K ↥(V ⊔ mulSub ℓ m) +
        Module.finrank K ↥(HS K M m ⊓ V.comap (LinearMap.mulLeft K ℓ)) =
      Module.finrank K ↥V + Module.finrank K ↥(HS K M m) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have h1 : HS K M m ⊓ V.comap (LinearMap.mulLeft K (0 : MvPolynomial (Fin M) K)) = HS K M m := by
      apply le_antisymm inf_le_left (le_inf le_rfl ?_)
      intro x _; simp
    rw [mulSub_zero, sup_bot_eq, h1]
  have hinj : Function.Injective (LinearMap.mulLeft K ℓ) := fun p q h => mul_left_cancel₀ hℓ h
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq V (mulSub ℓ m)
  have hinf : V ⊓ mulSub ℓ m = (HS K M m ⊓ V.comap (LinearMap.mulLeft K ℓ)).map (LinearMap.mulLeft K ℓ) := by
    apply le_antisymm
    · rintro x ⟨hxV, ⟨p, hp, rfl⟩⟩
      exact ⟨p, ⟨hp, hxV⟩, rfl⟩
    · rintro _ ⟨p, ⟨hp, hpV⟩, rfl⟩
      exact ⟨hpV, Submodule.mem_map_of_mem hp⟩
  rw [hinf, (Submodule.equivMapOfInjective _ hinj _).symm.finrank_eq, finrank_mulSub hℓ] at e1
  omega

theorem codim_eq_colon_add {m : ℕ} {V : Submodule K (MvPolynomial (Fin M) K)} (hV : V ≤ HS K M (m + 1))
    {ℓ : MvPolynomial (Fin M) K} (hℓ : ℓ ∈ HS K M 1) :
    codim K M (m + 1) V =
      codim K M m (HS K M m ⊓ V.comap (LinearMap.mulLeft K ℓ)) + codim K M (m + 1) (V ⊔ mulSub ℓ m) := by
  haveI : Module.Finite K ↥V := Module.Finite.of_injective _ (Submodule.inclusion_injective hV)
  have h := finrank_sup_mulSub_add (m := m) V ℓ
  have h1 : Module.finrank K ↥(V ⊔ mulSub ℓ m) ≤ Module.finrank K ↥(HS K M (m + 1)) :=
    finrank_le_of_le (sup_le hV (mulSub_le hℓ m))
  have h2 : Module.finrank K ↥(HS K M m ⊓ V.comap (LinearMap.mulLeft K ℓ)) ≤ Module.finrank K ↥(HS K M m) :=
    finrank_le_of_le inf_le_left
  have h3 : Module.finrank K ↥V ≤ Module.finrank K ↥(V ⊔ mulSub ℓ m) := Submodule.finrank_mono le_sup_left
  unfold codim
  omega

theorem exists_generic_codim (m : ℕ) (V : Submodule K (MvPolynomial (Fin M) K)) [Module.Finite K ↥V] :
    ∃ G : MvPolynomial (Fin M) K, G ≠ 0 ∧ ∀ a : Fin M → K, eval a G ≠ 0 →
      ∀ a' : Fin M → K, Module.finrank K ↥(V ⊔ mulSub (lin a') m) ≤ Module.finrank K ↥(V ⊔ mulSub (lin a) m) := by
  let g : Fin M → ↥(HS K M m) →ₗ[K] (MvPolynomial (Fin M) K ⧸ V) := fun i =>
    V.mkQ ∘ₗ (LinearMap.mulLeft K (X i)).domRestrict (HS K M m)
  have hfam : ∀ a, fam g a = V.mkQ ∘ₗ (LinearMap.mulLeft K (lin a)).domRestrict (HS K M m) := by
    intro a
    apply LinearMap.ext
    intro p
    rw [fam_apply]
    simp only [g, LinearMap.comp_apply, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, ← map_smul,
      ← map_sum]
    congr 1
    simp [lin, Finset.sum_mul, smul_eq_C_mul, mul_assoc]
  have hrange : ∀ a, LinearMap.range (fam g a) = (mulSub (lin a) m).map V.mkQ := by
    intro a
    rw [hfam, LinearMap.range_comp, LinearMap.range_domRestrict]
    rfl
  obtain ⟨G, hG, hmax⟩ := exists_generic_rank g
  refine ⟨G, hG, fun a ha a' => ?_⟩
  have := hmax a ha a'
  rw [hrange, hrange] at this
  rw [finrank_sup_eq, finrank_sup_eq]
  omega

variable [Infinite K]

theorem exists_eval_ne_zero {G : MvPolynomial (Fin M) K} (hG : G ≠ 0) : ∃ a : Fin M → K, eval a G ≠ 0 := by
  by_contra h
  push Not at h
  exact hG (MvPolynomial.funext fun x => by rw [h x, map_zero])

end Pieces

section Restrict

variable {K : Type} [Field K] {N : ℕ}

noncomputable def bvec (a : Fin (N + 1) → K) : Fin N → K := fun j => -(a (Fin.castSucc j) / a (Fin.last N))

noncomputable def θ (a : Fin (N + 1) → K) : Fin (N + 1) → MvPolynomial (Fin N) K :=
  Fin.snoc (fun j => X j) (lin (bvec a))

theorem θ_castSucc (a : Fin (N + 1) → K) (j : Fin N) : θ a (Fin.castSucc j) = X j := by
  simp [θ]

theorem θ_last (a : Fin (N + 1) → K) : θ a (Fin.last N) = lin (bvec a) := by
  simp [θ]

theorem θ_isHomogeneous (a : Fin (N + 1) → K) (i : Fin (N + 1)) : (θ a i).IsHomogeneous 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [θ_last]; exact lin_isHomogeneous _
  · rw [θ_castSucc]; exact isHomogeneous_X _ _

noncomputable def φ (a : Fin (N + 1) → K) : MvPolynomial (Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin N) K :=
  aeval (θ a)

theorem φ_mem {a : Fin (N + 1) → K} {m : ℕ} {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ HS K (N + 1) m) :
    φ a p ∈ HS K N m := by
  have := IsHomogeneous.aeval hp (θ a) (θ_isHomogeneous a)
  rwa [one_mul] at this

theorem map_φ_le (a : Fin (N + 1) → K) (m : ℕ) : (HS K (N + 1) m).map (φ a).toLinearMap ≤ HS K N m := by
  rintro _ ⟨p, hp, rfl⟩; exact φ_mem hp

theorem φ_rename (a : Fin (N + 1) → K) (q : MvPolynomial (Fin N) K) : φ a (rename Fin.castSucc q) = q := by
  unfold φ
  rw [aeval_rename]
  have : (θ a) ∘ Fin.castSucc = X := funext fun j => θ_castSucc a j
  rw [this, aeval_X_left_apply]

theorem map_φ_eq (a : Fin (N + 1) → K) (m : ℕ) : (HS K (N + 1) m).map (φ a).toLinearMap = HS K N m := by
  apply le_antisymm (map_φ_le a m)
  intro q hq
  exact ⟨rename Fin.castSucc q, IsHomogeneous.rename_isHomogeneous hq, φ_rename a q⟩

scoped instance finite_map_φ (a : Fin (N + 1) → K) (U : Submodule K (MvPolynomial (Fin (N + 1)) K))
    [Module.Finite K ↥U] : Module.Finite K ↥(U.map (φ a).toLinearMap) :=
  Module.Finite.map _ _

theorem φ_X_castSucc (a : Fin (N + 1) → K) (j : Fin N) : φ a (X (Fin.castSucc j)) = X j := by
  unfold φ; rw [aeval_X, θ_castSucc]

theorem φ_X_last (a : Fin (N + 1) → K) : φ a (X (Fin.last N)) = lin (bvec a) := by
  unfold φ; rw [aeval_X, θ_last]

theorem algHom_lin {M M' : ℕ} (f : MvPolynomial (Fin M) K →ₐ[K] MvPolynomial (Fin M') K) (a : Fin M → K) :
    f (lin a) = ∑ i, C (a i) * f (X i) := by
  simp [lin, map_sum, map_mul, algHom_C]

noncomputable def Lmap (a a' : Fin (N + 1) → K) : Fin N → K :=
  fun j => a' (Fin.castSucc j) + a' (Fin.last N) * bvec a j

theorem φ_lin (a a' : Fin (N + 1) → K) : φ a (lin a') = lin (Lmap a a') := by
  have hL : Lmap a a' = (fun j => a' (Fin.castSucc j)) + a' (Fin.last N) • bvec a := by
    funext j; simp [Lmap]
  rw [hL, lin_add, lin_smul, algHom_lin, Fin.sum_univ_castSucc]
  simp only [φ_X_castSucc, φ_X_last]
  rfl

theorem Lmap_self (a : Fin (N + 1) → K) (ha : a (Fin.last N) ≠ 0) : Lmap a a = 0 := by
  funext j
  simp only [Lmap, bvec, Pi.zero_apply, mul_neg, mul_div_cancel₀ _ ha]
  ring

theorem φ_lin_self (a : Fin (N + 1) → K) (ha : a (Fin.last N) ≠ 0) : φ a (lin a) = 0 := by
  rw [φ_lin, Lmap_self a ha, lin_zero]

theorem Lmap_snoc (a : Fin (N + 1) → K) (b : Fin N → K) : Lmap a (Fin.snoc b 0) = b := by
  funext j; simp [Lmap]

noncomputable def pull (a : Fin (N + 1) → K) (G : MvPolynomial (Fin N) K) : MvPolynomial (Fin (N + 1)) K :=
  bind₁ (fun j => X (Fin.castSucc j) + X (Fin.last N) * C (bvec a j)) G

theorem eval_pull (a a' : Fin (N + 1) → K) (G : MvPolynomial (Fin N) K) :
    eval a' (pull a G) = eval (Lmap a a') G := by
  unfold pull
  show eval₂Hom (RingHom.id K) a' (bind₁ _ G) = _
  rw [eval₂Hom_bind₁]
  show eval (fun j => eval a' (X (Fin.castSucc j) + X (Fin.last N) * C (bvec a j))) G = _
  have : (fun j => eval a' (X (Fin.castSucc j) + X (Fin.last N) * C (bvec a j))) = Lmap a a' := by
    funext j
    simp [Lmap]
  rw [this]

theorem pull_ne_zero [Infinite K] (a : Fin (N + 1) → K) {G : MvPolynomial (Fin N) K} (hG : G ≠ 0) :
    pull a G ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_eval_ne_zero hG
  intro h
  have := eval_pull a (Fin.snoc b 0) G
  rw [h, map_zero, Lmap_snoc] at this
  exact hb this.symm

theorem mem_mulSub_X_of_φ_eq_zero (a : Fin (N + 1) → K) (haX : φ a (X (Fin.last N)) = 0) {m : ℕ}
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ HS K (N + 1) (m + 1)) (h0 : φ a p = 0) :
    p ∈ mulSub (X (Fin.last N) : MvPolynomial (Fin (N + 1)) K) m := by
  classical
  set s : Fin (N + 1) →₀ ℕ := Finsupp.single (Fin.last N) 1 with hs
  set q := p.divMonomial s with hq
  set r := p.modMonomial s with hr
  have hpqr : X (Fin.last N) * q + r = p := divMonomial_add_modMonomial_single p (Fin.last N)

  have hrvars : (↑r.vars : Set (Fin (N + 1))) ⊆ Set.range Fin.castSucc := by
    intro i hi
    rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
    obtain ⟨d, hd, hid⟩ := hi
    have hcoeff : coeff d r ≠ 0 := mem_support_iff.mp hd
    have hnle : ¬ s ≤ d := fun hle => hcoeff (coeff_modMonomial_of_le p hle)
    have hdN : d (Fin.last N) = 0 := by
      rw [hs, Finsupp.single_le_iff] at hnle; omega
    have hi : i ≠ Fin.last N := by
      rintro rfl; exact (Finsupp.mem_support_iff.mp hid) hdN
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    exact ⟨j, rfl⟩
  obtain ⟨r', hr'⟩ := exists_rename_eq_of_vars_subset_range r Fin.castSucc (Fin.castSucc_injective N) hrvars
  have hr0 : r = 0 := by
    have h1 : φ a p = r' := by
      rw [← hpqr, map_add, map_mul, haX, zero_mul, zero_add, ← hr', φ_rename]
    rw [h0] at h1
    rw [← hr', ← h1, map_zero]
  rw [hr0, add_zero] at hpqr

  have hqm : q ∈ HS K (N + 1) m := by
    intro d hd
    rw [hq, coeff_divMonomial] at hd
    have h1 := hp hd
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h1 ⊢
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hs, Finsupp.sum_single_index rfl] at h1
    omega
  rw [← hpqr]
  exact mul_mem_mulSub _ hqm

section Kernel

variable (a : Fin (N + 1) → K)

noncomputable def gA (m : ℕ) : ↥(HS K (N + 1) (m + 1)) →ₗ[K] MvPolynomial (Fin N) K :=
  (φ a).toLinearMap.domRestrict (HS K (N + 1) (m + 1))

theorem finrank_ker_gA (m : ℕ) :
    Module.finrank K ↥(HS K N (m + 1)) + Module.finrank K ↥(LinearMap.ker (gA a m)) =
      Module.finrank K ↥(HS K (N + 1) (m + 1)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (gA a m)
  rw [gA, LinearMap.range_domRestrict, map_φ_eq] at h
  exact h

noncomputable def BA (m : ℕ) : Submodule K ↥(HS K (N + 1) (m + 1)) :=
  (mulSub (lin a) m).comap (HS K (N + 1) (m + 1)).subtype

variable {a}

theorem BA_le_ker (ha : a (Fin.last N) ≠ 0) (m : ℕ) : BA a m ≤ LinearMap.ker (gA a m) := by
  rintro ⟨p, hp⟩ hB
  obtain ⟨q, _, hq⟩ := (mem_mulSub_iff _ _ _).mp hB
  have hq' : lin a * q = p := hq
  simp only [LinearMap.mem_ker, gA, LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply]
  rw [← hq', map_mul, φ_lin_self a ha, zero_mul]

theorem finrank_BA (ha : a (Fin.last N) ≠ 0) (m : ℕ) :
    Module.finrank K ↥(BA a m) = Module.finrank K ↥(HS K (N + 1) m) := by
  rw [BA, (Submodule.comapSubtypeEquivOfLe (mulSub_le (lin_mem a) m)).finrank_eq,
    finrank_mulSub (lin_ne_zero ha)]

end Kernel

theorem finrank_HS_succ (m : ℕ) :
    Module.finrank K ↥(HS K (N + 1) (m + 1)) =
      Module.finrank K ↥(HS K N (m + 1)) + Module.finrank K ↥(HS K (N + 1) m) := by
  classical
  set e : Fin (N + 1) → K := Pi.single (Fin.last N) 1 with he
  have heN : e (Fin.last N) ≠ 0 := by simp [he]
  have hle : lin e = X (Fin.last N) := lin_single (Fin.last N)
  have hker : LinearMap.ker (gA e m) = BA e m := by
    apply le_antisymm _ (BA_le_ker heN m)
    rintro ⟨p, hp⟩ hk
    simp only [LinearMap.mem_ker, gA, LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply] at hk
    show p ∈ mulSub (lin e) m
    rw [hle]
    refine mem_mulSub_X_of_φ_eq_zero e ?_ hp hk
    rw [← hle]; exact φ_lin_self e heN
  have h := finrank_ker_gA e m
  rw [hker, finrank_BA heN] at h
  exact h.symm

theorem φ_eq_zero_iff {a : Fin (N + 1) → K} (ha : a (Fin.last N) ≠ 0) {m : ℕ}
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ HS K (N + 1) (m + 1)) :
    φ a p = 0 ↔ p ∈ mulSub (lin a) m := by
  have hker : BA a m = LinearMap.ker (gA a m) := by
    apply Submodule.eq_of_le_of_finrank_eq (BA_le_ker ha m)
    have h1 := finrank_ker_gA a m
    have h2 := finrank_HS_succ (K := K) (N := N) m
    rw [finrank_BA ha]
    omega
  constructor
  · intro h0
    have : (⟨p, hp⟩ : ↥(HS K (N + 1) (m + 1))) ∈ LinearMap.ker (gA a m) := by
      simp only [LinearMap.mem_ker, gA, LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply]; exact h0
    rw [← hker] at this
    exact this
  · intro hB
    have : (⟨p, hp⟩ : ↥(HS K (N + 1) (m + 1))) ∈ LinearMap.ker (gA a m) := by rw [← hker]; exact hB
    simpa [gA] using this

theorem codim_map_φ (a : Fin (N + 1) → K) (ha : a (Fin.last N) ≠ 0) {m : ℕ}
    {U : Submodule K (MvPolynomial (Fin (N + 1)) K)} (h1 : mulSub (lin a) m ≤ U) (h2 : U ≤ HS K (N + 1) (m + 1)) :
    codim K N (m + 1) (U.map (φ a).toLinearMap) = codim K (N + 1) (m + 1) U := by
  haveI : Module.Finite K ↥U := Module.Finite.of_injective _ (Submodule.inclusion_injective h2)
  have hU := finrank_map_add (φ a).toLinearMap U (mulSub (lin a) m) h1
    (fun x hx => φ_eq_zero_iff ha (h2 hx))
  rw [finrank_mulSub (lin_ne_zero ha)] at hU
  have hS := finrank_HS_succ (K := K) (N := N) m
  have h3 : Module.finrank K ↥(U.map (φ a).toLinearMap) ≤ Module.finrank K ↥(HS K N (m + 1)) :=
    finrank_le_of_le ((Submodule.map_mono h2).trans (map_φ_le a _))
  unfold codim
  omega

theorem map_mulSub (a : Fin (N + 1) → K) (ℓ : MvPolynomial (Fin (N + 1)) K) (m : ℕ) :
    (mulSub ℓ m).map (φ a).toLinearMap = mulSub (φ a ℓ) m := by
  unfold mulSub
  rw [← map_φ_eq a m, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro p
  simp

theorem map_colon_le (a : Fin (N + 1) → K) {m : ℕ} (V : Submodule K (MvPolynomial (Fin (N + 1)) K))
    (ℓ : MvPolynomial (Fin (N + 1)) K) :
    (HS K (N + 1) m ⊓ V.comap (LinearMap.mulLeft K ℓ)).map (φ a).toLinearMap ≤
      HS K N m ⊓ (V.map (φ a).toLinearMap).comap (LinearMap.mulLeft K (φ a ℓ)) := by
  rintro _ ⟨p, ⟨hp, hpV⟩, rfl⟩
  refine ⟨φ_mem hp, ?_⟩
  refine ⟨ℓ * p, hpV, ?_⟩
  simp

end Restrict

section Main

variable {K : Type} [Field K]

theorem macaulayPow_one (a : ℕ) : Nat.macaulayPow 1 a = (a + 1).choose 2 := by
  have h0 : ∀ b, Nat.macaulayPow 0 b = 0 := fun b => by simp [Nat.macaulayPow]
  have hfg : Nat.findGreatest (fun k => k.choose (0 + 1) ≤ a) (a + 0 + 1) = a := by
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun _ => by simp, fun n hn _ => by simp; omega⟩
  show Nat.macaulayPow (0 + 1) a = _
  rw [Nat.macaulayPow, hfg, h0]
  rfl

theorem HS_zero_vars (m : ℕ) : HS K 0 (m + 1) = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Submodule.mem_bot]
  ext d
  obtain rfl : d = 0 := Subsingleton.elim d 0
  rw [coeff_zero]
  by_contra h
  have := hp h
  simp at this

variable [Infinite K]

theorem main : ∀ (M e : ℕ) (V : Submodule K (MvPolynomial (Fin M) K)), V ≤ HS K M (e + 1) →
    ∃ G : MvPolynomial (Fin M) K, G ≠ 0 ∧ ∀ a : Fin M → K, eval a G ≠ 0 →
      Nat.macaulayPow (e + 1) (codim K M (e + 1) (V ⊔ mulSub (lin a) e)) + codim K M (e + 1) V ≤
        Nat.macaulayPow (e + 1) (codim K M (e + 1) V) := by
  intro M
  induction M with
  | zero =>
      intro e V _
      refine ⟨1, one_ne_zero, fun a _ => ?_⟩
      have hbot : ∀ W : Submodule K (MvPolynomial (Fin 0) K), codim K 0 (e + 1) W = 0 := by
        intro W
        unfold codim
        rw [HS_zero_vars, finrank_bot, Nat.zero_sub]
      rw [hbot, hbot, add_zero]
  | succ N ihN =>
      intro e
      induction e with
      | zero =>

          intro V hV
          haveI : Module.Finite K ↥V := Module.Finite.of_injective _ (Submodule.inclusion_injective hV)
          obtain ⟨G₀, hG₀, hmin⟩ := exists_generic_codim 0 V
          refine ⟨G₀, hG₀, fun a ha => ?_⟩
          have hle : ∀ b : Fin (N + 1) → K, V ⊔ mulSub (lin b) 0 ≤ HS K (N + 1) (0 + 1) := fun b =>
            sup_le hV (mulSub_le (lin_mem b) 0)
          set x := codim K (N + 1) (0 + 1) (V ⊔ mulSub (lin a) 0) with hx
          set c := codim K (N + 1) (0 + 1) V with hc
          rw [macaulayPow_one, macaulayPow_one]
          have hpasc : (c + 1).choose 2 = c + c.choose 2 := by
            have := Nat.choose_succ_succ' c 1; rw [Nat.choose_one_right] at this; exact this
          by_cases hVtop : HS K (N + 1) (0 + 1) ≤ V
          · have h1 : Module.finrank K ↥V = Module.finrank K ↥(HS K (N + 1) (0 + 1)) :=
              le_antisymm (finrank_le_of_le hV) (Submodule.finrank_mono hVtop)
            have h2 := finrank_le_of_le (hle a)
            have h3 : Module.finrank K ↥V ≤ Module.finrank K ↥(V ⊔ mulSub (lin a) 0) :=
              Submodule.finrank_mono le_sup_left
            have hx0 : x = 0 := by rw [hx]; unfold codim; omega
            have hc0 : c = 0 := by rw [hc]; unfold codim; omega
            rw [hx0, hc0]
            decide
          · obtain ⟨p, hp1, hpV⟩ := Set.not_subset.mp hVtop
            set b : Fin (N + 1) → K := fun i => coeff (Finsupp.single i 1) p with hb
            have hpb : p = lin b := eq_lin_of_mem_one hp1
            have hlt : V < V ⊔ mulSub (lin b) 0 := by
              refine lt_of_le_of_ne le_sup_left fun h => hpV ?_
              rw [h, hpb]
              refine Submodule.mem_sup_right ?_
              have : lin b * 1 ∈ mulSub (lin b) 0 := mul_mem_mulSub _ (isHomogeneous_one (Fin (N + 1)) K)
              rwa [mul_one] at this
            have h1 := Submodule.finrank_lt_finrank_of_lt hlt
            have h2 := hmin a ha b
            have h3 := finrank_le_of_le (hle a)
            have hxc : x + 1 ≤ c := by rw [hx, hc]; unfold codim; omega
            have h4 : (x + 1).choose 2 ≤ c.choose 2 := Nat.choose_le_choose 2 hxc
            omega
      | succ e ihe =>
          intro V hV
          haveI : Module.Finite K ↥V := Module.Finite.of_injective _ (Submodule.inclusion_injective hV)
          obtain ⟨G₀, hG₀, hmin⟩ := exists_generic_codim (e + 1) V
          refine ⟨G₀, hG₀, fun a ha => ?_⟩
          have hle : ∀ b : Fin (N + 1) → K, V ⊔ mulSub (lin b) (e + 1) ≤ HS K (N + 1) (e + 1 + 1) := fun b =>
            sup_le hV (mulSub_le (lin_mem b) (e + 1))
          set x := codim K (N + 1) (e + 1 + 1) (V ⊔ mulSub (lin a) (e + 1)) with hx
          set c := codim K (N + 1) (e + 1 + 1) V with hc

          have hxeq : ∀ b, eval b G₀ ≠ 0 → codim K (N + 1) (e + 1 + 1) (V ⊔ mulSub (lin b) (e + 1)) = x := by
            intro b hb
            have h1 := hmin a ha b
            have h2 := hmin b hb a
            rw [hx]; unfold codim; omega

          obtain ⟨a', ha'⟩ := exists_eval_ne_zero (mul_ne_zero hG₀ (X_ne_zero (Fin.last N)) :
            G₀ * X (Fin.last N) ≠ 0)
          rw [map_mul, eval_X] at ha'
          have ha'G : eval a' G₀ ≠ 0 := left_ne_zero_of_mul ha'
          have ha'N : a' (Fin.last N) ≠ 0 := right_ne_zero_of_mul ha'
          have hxa' : codim K (N + 1) (e + 1 + 1) (V ⊔ mulSub (lin a') (e + 1)) = x := hxeq a' ha'G

          set V₁ := V.map (φ a').toLinearMap with hV₁
          have hV₁le : V₁ ≤ HS K N (e + 1 + 1) := (Submodule.map_mono hV).trans (map_φ_le a' _)
          have hcV₁ : codim K N (e + 1 + 1) V₁ = x := by
            rw [← hxa', ← codim_map_φ a' ha'N (m := e + 1) (U := V ⊔ mulSub (lin a') (e + 1)) le_sup_right (hle a'),
              Submodule.map_sup, map_mulSub, φ_lin_self a' ha'N, mulSub_zero, sup_bot_eq]
          obtain ⟨G₁, hG₁, hG₁spec⟩ := ihN (e + 1) V₁ hV₁le

          set W' := HS K (N + 1) (e + 1) ⊓ V.comap (LinearMap.mulLeft K (lin a')) with hW'
          have hW'le : W' ≤ HS K (N + 1) (e + 1) := inf_le_left
          set y := codim K (N + 1) (e + 1) W' with hy
          have hcxy : c = y + x := by
            rw [hc, hy, ← hxa']; exact codim_eq_colon_add hV (lin_mem a')
          obtain ⟨G₂, hG₂, hG₂spec⟩ := ihe W' hW'le

          have hP : G₀ * pull a' G₁ * G₂ * X (Fin.last N) ≠ 0 :=
            mul_ne_zero (mul_ne_zero (mul_ne_zero hG₀ (pull_ne_zero a' hG₁)) hG₂) (X_ne_zero _)
          obtain ⟨a'', ha''⟩ := exists_eval_ne_zero hP
          simp only [map_mul, eval_X, mul_ne_zero_iff] at ha''
          obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := ha''
          rw [eval_pull] at h1
          have hxa'' : codim K (N + 1) (e + 1 + 1) (V ⊔ mulSub (lin a'') (e + 1)) = x := hxeq a'' h0

          set u := codim K (N + 1) (e + 1) (W' ⊔ mulSub (lin a'') e) with hu
          have hu_ineq : Nat.macaulayPow (e + 1) u + y ≤ Nat.macaulayPow (e + 1) y := hG₂spec a'' h2
          set v := codim K N (e + 1 + 1) (V₁ ⊔ mulSub (lin (Lmap a' a'')) (e + 1)) with hv
          have hv_ineq : Nat.macaulayPow (e + 1 + 1) v + x ≤ Nat.macaulayPow (e + 1 + 1) x := by
            have := hG₁spec (Lmap a' a'') h1; rwa [hcV₁] at this

          have hchain : x ≤ u + v := by
            set V₂ := V.map (φ a'').toLinearMap with hV₂
            have hV₂le : V₂ ≤ HS K N (e + 1 + 1) := (Submodule.map_mono hV).trans (map_φ_le a'' _)
            have hxV₂ : codim K N (e + 1 + 1) V₂ = x := by
              rw [← hxa'', ← codim_map_φ a'' h3 (m := e + 1) (U := V ⊔ mulSub (lin a'') (e + 1)) le_sup_right
                (hle a''), Submodule.map_sup, map_mulSub, φ_lin_self a'' h3, mulSub_zero, sup_bot_eq]

            have hℓT : φ a'' (lin a') ∈ HS K N 1 := φ_mem (lin_mem a')
            have hcount := codim_eq_colon_add (m := e + 1) hV₂le hℓT

            have h5a : codim K N (e + 1) (HS K N (e + 1) ⊓ V₂.comap (LinearMap.mulLeft K (φ a'' (lin a')))) ≤ u := by
              haveI : Module.Finite K ↥(HS K N (e + 1) ⊓ V₂.comap (LinearMap.mulLeft K (φ a'' (lin a')))) :=
                Module.Finite.of_injective _ (Submodule.inclusion_injective inf_le_left)
              have hfin : Module.finrank K ↥(W'.map (φ a'').toLinearMap) ≤
                  Module.finrank K ↥(HS K N (e + 1) ⊓ V₂.comap (LinearMap.mulLeft K (φ a'' (lin a')))) :=
                Submodule.finrank_mono (map_colon_le a'' (m := e + 1) V (lin a'))
              have hu' : u = codim K N (e + 1) (W'.map (φ a'').toLinearMap) := by
                rw [hu, ← codim_map_φ a'' h3 (m := e) (U := W' ⊔ mulSub (lin a'') e) le_sup_right
                  (sup_le hW'le (mulSub_le (lin_mem a'') e)), Submodule.map_sup, map_mulSub, φ_lin_self a'' h3,
                  mulSub_zero, sup_bot_eq]
              rw [hu']; unfold codim; omega

            have hle3 : V ⊔ mulSub (lin a'') (e + 1) ⊔ mulSub (lin a') (e + 1) ≤ HS K (N + 1) (e + 1 + 1) :=
              sup_le (hle a'') (mulSub_le (lin_mem a') _)
            have h5b : codim K N (e + 1 + 1) (V₂ ⊔ mulSub (φ a'' (lin a')) (e + 1)) = v := by
              have eS : codim K N (e + 1 + 1) (V₂ ⊔ mulSub (φ a'' (lin a')) (e + 1)) =
                  codim K (N + 1) (e + 1 + 1) (V ⊔ mulSub (lin a'') (e + 1) ⊔ mulSub (lin a') (e + 1)) := by
                rw [← codim_map_φ a'' h3 (m := e + 1) (U := V ⊔ mulSub (lin a'') (e + 1) ⊔ mulSub (lin a') (e + 1))
                  (le_sup_right.trans le_sup_left) hle3, Submodule.map_sup, Submodule.map_sup, map_mulSub,
                  map_mulSub, φ_lin_self a'' h3, mulSub_zero, sup_bot_eq]
              have eS' : v = codim K (N + 1) (e + 1 + 1) (V ⊔ mulSub (lin a'') (e + 1) ⊔ mulSub (lin a') (e + 1)) := by
                rw [hv, hV₁, ← φ_lin a' a'', sup_right_comm,
                  ← codim_map_φ a' ha'N (m := e + 1) (U := V ⊔ mulSub (lin a') (e + 1) ⊔ mulSub (lin a'') (e + 1))
                  (le_sup_right.trans le_sup_left) (by rw [sup_right_comm]; exact hle3), Submodule.map_sup,
                  Submodule.map_sup, map_mulSub, map_mulSub, φ_lin_self a' ha'N, mulSub_zero, sup_bot_eq]
              rw [eS, eS']
            rw [hxV₂, h5b] at hcount
            omega

          have key := Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add (e + 1) x y u v (Nat.succ_pos e)
            hchain hu_ineq hv_ineq
          rw [hcxy, Nat.add_comm y x]
          exact key

end Main

section Ideals

variable {K : Type} [Field K] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry.HilbertFunctor

theorem finrank_piece_eq_codim (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (m : ℕ) :
    Module.finrank K (piece I m) = codim K (n + 1) m (HS K (n + 1) m ⊓ I.restrictScalars K) := by
  have h : Module.finrank K (piece I m) +
      Module.finrank K ↥(Submodule.comap (HS K (n + 1) m).subtype (I.restrictScalars K)) =
      Module.finrank K ↥(HS K (n + 1) m) := Submodule.finrank_quotient_add_finrank _
  have hc : Submodule.comap (HS K (n + 1) m).subtype (I.restrictScalars K) =
      Submodule.comap (HS K (n + 1) m).subtype (HS K (n + 1) m ⊓ I.restrictScalars K) := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have hf : Module.finrank K ↥(Submodule.comap (HS K (n + 1) m).subtype (I.restrictScalars K)) =
      Module.finrank K ↥(HS K (n + 1) m ⊓ I.restrictScalars K) := by
    rw [hc]; exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  rw [hf] at h
  unfold codim
  omega

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) K) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) K) q d : MvPolynomial (Fin (n + 1)) K) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_add {G : MvPolynomial (Fin (n + 1)) K} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) K) (d : ℕ) :
    homogeneousComponent (m + d) (a * G) = homogeneousComponent d a * G := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) K)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) K m from hG) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem HS_inf_sup_span {J : Ideal (MvPolynomial (Fin (n + 1)) K)}
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) (a : Fin (n + 1) → K) (e : ℕ) :
    HS K (n + 1) (e + 1) ⊓ (J ⊔ Ideal.span {lin a}).restrictScalars K =
      (HS K (n + 1) (e + 1) ⊓ J.restrictScalars K) ⊔ mulSub (lin a) e := by
  apply le_antisymm
  · rintro x ⟨hx, hxJ⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hx1 : y + g * lin a = homogeneousComponent (e + 1) (y + g * lin a) := by
      rw [homogeneousComponent_of_mem hx, if_pos rfl]
    have hgl : homogeneousComponent (e + 1) (g * lin a) = homogeneousComponent e g * lin a := by
      rw [Nat.add_comm e 1]; exact homogeneousComponent_mul_add (lin_isHomogeneous a) g e
    rw [hx1, map_add, hgl]
    refine Submodule.add_mem_sup ⟨homogeneousComponent_isHomogeneous _ _, hJ y hy _⟩ ?_
    rw [mul_comm]
    exact mul_mem_mulSub _ (homogeneousComponent_isHomogeneous e g)
  · refine sup_le (inf_le_inf_left _ ?_) ?_
    · exact fun x hx => Submodule.mem_sup_left hx
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨mulSub_le (lin_mem a) e (mul_mem_mulSub _ hp), ?_⟩
      show lin a * p ∈ J ⊔ Ideal.span {lin a}
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end Ideals

end GreenHRT
p2m_reactivate "P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.GreenHRT"

open MvPolynomial AlgebraicGeometry.HilbertFunctor GreenHRT in

theorem solution (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      Nat.macaulayPow d (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) d)) +
          Module.finrank K (piece J d) ≤
        Nat.macaulayPow d (Module.finrank K (piece J d)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨G, hG, hspec⟩ := main (n + 1) e (HS K (n + 1) (e + 1) ⊓ J.restrictScalars K) inf_le_left
  refine ⟨G, hG, fun a ha => ?_⟩
  have h1 := finrank_piece_eq_codim (K := K) J (e + 1)
  have h2 : Module.finrank K (piece (J ⊔ Ideal.span {lin a}) (e + 1)) =
      codim K (n + 1) (e + 1) ((HS K (n + 1) (e + 1) ⊓ J.restrictScalars K) ⊔ mulSub (lin a) e) := by
    rw [finrank_piece_eq_codim, HS_inf_sup_span hJ a e]
  have := hspec a ha
  rw [← h1, ← h2] at this
  exact this

end S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
end P2MW
export P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le (solution)
