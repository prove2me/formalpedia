-- Prove2me | solution 1 for HeckeEis.span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/105470b7-9f40-5e54-a1c4-6c2c5ce1c8de

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top

set_option autoImplicit false

namespace HBSP

open CongruenceSubgroup HeckeEis MvPolynomial
open scoped MatrixGroups

section MapA

variable {R R' : Type*} [CommRing R] [CommRing R']

noncomputable def mapA (c : R →+ R') (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R' :=
  AddMonoidAlgebra.map c P

@[scoped simp] theorem coeff_mapA (c : R →+ R') (P : MvPolynomial (Fin 2) R) (m : Fin 2 →₀ ℕ) :
    coeff m (mapA c P) = c (coeff m P) :=
  rfl

theorem mapA_add (c : R →+ R') (P Q : MvPolynomial (Fin 2) R) : mapA c (P + Q) = mapA c P + mapA c Q := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_mapA, coeff_add, map_add]

theorem mapA_sub (c : R →+ R') (P Q : MvPolynomial (Fin 2) R) : mapA c (P - Q) = mapA c P - mapA c Q := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_mapA, coeff_sub, map_sub]

theorem mapA_zero (c : R →+ R') : mapA c (0 : MvPolynomial (Fin 2) R) = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_mapA, coeff_zero, map_zero]

theorem mapA_sum (c : R →+ R') {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Fin 2) R) :
    mapA c (∑ i ∈ s, P i) = ∑ i ∈ s, mapA c (P i) := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_mapA, coeff_sum, map_sum]

theorem mapA_ringHom (φ : R →+* R') (P : MvPolynomial (Fin 2) R) : mapA φ.toAddMonoidHom P = map φ P := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_mapA, coeff_map]
  rfl

theorem isHomogeneous_mapA (c : R →+ R') {P : MvPolynomial (Fin 2) R} {n : ℕ} (hP : P.IsHomogeneous n) :
    (mapA c P).IsHomogeneous n := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_mapA, h0, map_zero]

theorem mapA_mem (c : R →+ R') {n : ℕ} {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    mapA c P ∈ BinaryForm R' n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  exact isHomogeneous_mapA c hP

theorem map_binarySubst (φ : R →+* R') (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    map φ (binarySubst R M P) = binarySubst R' M (map φ P) := by
  have h : (map φ).comp (binarySubst R M : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R) =
      (binarySubst R' M : MvPolynomial (Fin 2) R' →+* MvPolynomial (Fin 2) R').comp (map φ) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_C, map_C]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_X, map_X, map_sum, map_mul, map_intCast]
  exact congrFun (congrArg DFunLike.coe h) P

noncomputable def Nz (M : Matrix (Fin 2) (Fin 2) ℤ) (e d : Fin 2 →₀ ℕ) : ℤ :=
  coeff d (binarySubst ℤ M (monomial e 1))

theorem coeff_binarySubst_monomial_one (M : Matrix (Fin 2) (Fin 2) ℤ) (e d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M (monomial e 1)) = (Nz M e d : R) := by
  have h : binarySubst R M (monomial e 1) = map (Int.castRingHom R) (binarySubst ℤ M (monomial e 1)) := by
    rw [map_binarySubst, MvPolynomial.map_monomial, (Int.castRingHom R).map_one]
  rw [h, coeff_map, Nz, eq_intCast]

theorem coeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M P) = ∑ e ∈ P.support, coeff e P * (Nz M e d : R) := by
  conv_lhs => rw [P.as_sum, map_sum]
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show monomial e (coeff e P) = coeff e P • monomial e (1 : R) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coeff_smul, coeff_binarySubst_monomial_one, smul_eq_mul]

theorem mapA_binarySubst (c : R →+ R') (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    mapA c (binarySubst R M P) = binarySubst R' M (mapA c P) := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_mapA, coeff_binarySubst, coeff_binarySubst, map_sum]
  have hsub : (mapA c P).support ⊆ P.support := Finsupp.support_mapRange (hf := c.map_zero)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [coeff_mapA, mul_comm (coeff e P), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  · intro e _ he
    have h0 : coeff e (mapA c P) = 0 := by
      simpa [MvPolynomial.mem_support_iff] using he
    rw [mul_comm (coeff e P), ← zsmul_eq_mul, map_zsmul, ← coeff_mapA, h0, smul_zero]

end MapA

section Cochains

variable {R R' : Type*} [CommRing R] [CommRing R'] (N n : ℕ)

noncomputable abbrev ρSym (R : Type*) [CommRing R] (N n : ℕ) : Representation R (Gamma0 N) ↥(BinaryForm R n) :=
  (binaryFormRepSL R n).comp (Gamma0 N).subtype

variable {N n}

noncomputable def cmap (c : R →+ R') (z : Gamma0 N → ↥(BinaryForm R n)) : Gamma0 N → ↥(BinaryForm R' n) :=
  fun g => ⟨mapA c ((z g : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R), mapA_mem c (z g).2⟩

@[scoped simp] theorem coe_cmap (c : R →+ R') (z : Gamma0 N → ↥(BinaryForm R n)) (g : Gamma0 N) :
    ((cmap c z g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = mapA c (z g : MvPolynomial (Fin 2) R) := rfl

theorem coe_ρSym_apply (R : Type*) [CommRing R] (g : Gamma0 N) (v : ↥(BinaryForm R n)) :
    ((ρSym R N n g v : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R) =
      binarySubst R ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) v := rfl

theorem cmap_mem_coeffCocycles (c : R →+ R') {z : Gamma0 N → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCocycles (ρSym R N n)) : cmap c z ∈ coeffCocycles (ρSym R' N n) := by
  intro g h
  apply Subtype.ext
  rw [Submodule.coe_add, coe_cmap, coe_cmap, coe_ρSym_apply, coe_cmap, hz g h, Submodule.coe_add, mapA_add,
    coe_ρSym_apply, mapA_binarySubst]

theorem cmap_mem_coeffCoboundaries (c : R →+ R') {z : Gamma0 N → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCoboundaries (ρSym R N n)) : cmap c z ∈ coeffCoboundaries (ρSym R' N n) := by
  rw [mem_coeffCoboundaries_iff] at hz ⊢
  obtain ⟨v, rfl⟩ := hz
  refine ⟨⟨mapA c (v : MvPolynomial (Fin 2) R), mapA_mem c v.2⟩, funext fun g => Subtype.ext ?_⟩
  rw [coe_cmap, Submodule.coe_sub, Submodule.coe_sub, coe_ρSym_apply, coe_ρSym_apply, mapA_sub, mapA_binarySubst]

theorem cmap_add (c : R →+ R') (z w : Gamma0 N → ↥(BinaryForm R n)) : cmap c (z + w) = cmap c z + cmap c w := by
  funext g; apply Subtype.ext
  simp only [coe_cmap, Pi.add_apply, Submodule.coe_add, mapA_add]

theorem coe_cmap_ringHom (φ : R →+* R') (z : Gamma0 N → ↥(BinaryForm R n)) (g : Gamma0 N) :
    ((cmap φ.toAddMonoidHom z g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = map φ (z g : MvPolynomial (Fin 2) R) := by
  rw [coe_cmap, mapA_ringHom]

end Cochains

section Denominators

variable {N n : ℕ}

theorem cocycle_apply_eq_zero_of_closure {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    {G : Type*} [Group G] (ρ : Representation K G V)
    (z : ↥(coeffCocycles ρ)) (S : Set G) (hS : ∀ s ∈ S, (z : G → V) s = 0)
    (g : G) (hg : g ∈ Subgroup.closure S) : (z : G → V) g = 0 := by
  have hz := z.2
  have h1 : (z : G → V) 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ ihx ihy => rw [hz x y, ihx, ihy, map_zero, zero_add]
  | inv x _ ih =>
    have h := hz x x⁻¹
    rw [mul_inv_cancel, h1, ih, zero_add] at h
    have h2 : ρ x⁻¹ (ρ x ((z : G → V) x⁻¹)) = 0 := by rw [← h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

def IsInt (v : ↥(BinaryForm ℚ n)) : Prop :=
  ∃ v₀ : ↥(BinaryForm ℤ n), map (Int.castRingHom ℚ) (v₀ : MvPolynomial (Fin 2) ℤ) = v

theorem IsInt.zero : IsInt (0 : ↥(BinaryForm ℚ n)) := ⟨0, by simp⟩

theorem IsInt.add {v w : ↥(BinaryForm ℚ n)} (hv : IsInt v) (hw : IsInt w) : IsInt (v + w) := by
  obtain ⟨v₀, hv₀⟩ := hv
  obtain ⟨w₀, hw₀⟩ := hw
  exact ⟨v₀ + w₀, by rw [Submodule.coe_add, map_add, hv₀, hw₀, Submodule.coe_add]⟩

theorem IsInt.neg {v : ↥(BinaryForm ℚ n)} (hv : IsInt v) : IsInt (-v) := by
  obtain ⟨v₀, hv₀⟩ := hv
  exact ⟨-v₀, by rw [Submodule.coe_neg, map_neg, hv₀, Submodule.coe_neg]⟩

theorem IsInt.rho {v : ↥(BinaryForm ℚ n)} (hv : IsInt v) (g : Gamma0 N) : IsInt (ρSym ℚ N n g v) := by
  obtain ⟨v₀, hv₀⟩ := hv
  refine ⟨ρSym ℤ N n g v₀, ?_⟩
  rw [coe_ρSym_apply, coe_ρSym_apply, map_binarySubst, hv₀]

theorem exists_int_multiple {ι : Type*} (s : Finset ι) (v : ι → ↥(BinaryForm ℚ n)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ i ∈ s, IsInt ((d : ℚ) • v i) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    (s.biUnion fun i => ((v i : MvPolynomial (Fin 2) ℚ).support.image fun m => (v i : MvPolynomial (Fin 2) ℚ).coeff m))
  have hb0 : ((b : ℤ)) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  choose! c hc using hb
  refine ⟨b, hb0, fun i hi => ⟨⟨∑ m ∈ (v i : MvPolynomial (Fin 2) ℚ).support,
      monomial m (c ((v i : MvPolynomial (Fin 2) ℚ).coeff m)), ?_⟩, ?_⟩⟩
  · rw [mem_homogeneousSubmodule]
    refine IsHomogeneous.sum _ _ _ fun m hm => ?_
    have hv := (mem_homogeneousSubmodule n _).mp (v i).2
    have hdeg := hv (mem_support_iff.mp hm)
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]; exact hdeg
  · simp only [map_sum, map_monomial]
    rw [Submodule.coe_smul]
    conv_rhs => rw [(v i : MvPolynomial (Fin 2) ℚ).as_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h := hc _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ hm⟩)
    rw [smul_monomial, eq_intCast]
    rw [eq_intCast] at h
    rw [h, zsmul_eq_mul, smul_eq_mul]

theorem exists_int_cocycle [NeZero N] (y : ↥(coeffCocycles (ρSym ℚ N n))) :
    ∃ (d : ℤ) (z₀ : ↥(coeffCocycles (ρSym ℤ N n))), d ≠ 0 ∧ ∀ g : Gamma0 N,
      map (Int.castRingHom ℚ) (((z₀ : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ) =
        (d : ℚ) • (((y : Gamma0 N → ↥(BinaryForm ℚ n)) g : ↥(BinaryForm ℚ n)) : MvPolynomial (Fin 2) ℚ) := by
  classical
  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  obtain ⟨S, hS⟩ := hΓ.out
  have hy := y.2
  obtain ⟨d, hd, hdS⟩ := exists_int_multiple (n := n) S (fun s : Gamma0 N => y.1 s)

  have hy1 : (y : Gamma0 N → ↥(BinaryForm ℚ n)) 1 = 0 := by
    have h := hy 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    have : y.1 1 + y.1 1 = y.1 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hall : ∀ g : Gamma0 N, IsInt ((d : ℚ) • (y : Gamma0 N → ↥(BinaryForm ℚ n)) g) := by
    intro g
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hdS x hx
    | one => rw [hy1, smul_zero]; exact IsInt.zero
    | mul a b _ _ iha ihb =>
      rw [hy a b, smul_add, ← map_smul]
      exact iha.add (ihb.rho a)
    | inv x _ ih =>
      have h := hy x x⁻¹
      rw [mul_inv_cancel, hy1] at h
      have hx : (y : Gamma0 N → ↥(BinaryForm ℚ n)) x⁻¹ = -(ρSym ℚ N n x⁻¹ ((y : Gamma0 N → _) x)) := by
        have h2 : ρSym ℚ N n x⁻¹ ((y : Gamma0 N → _) x + ρSym ℚ N n x ((y : Gamma0 N → _) x⁻¹)) = 0 := by
          rw [← h, map_zero]
        rw [map_add, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
        exact eq_neg_of_add_eq_zero_right h2
      rw [hx, smul_neg, ← map_smul]
      exact (ih.rho x⁻¹).neg
  choose v₀ hv₀ using hall
  refine ⟨d, ⟨v₀, fun g h => ?_⟩, hd, fun g => ?_⟩
  ·
    apply Subtype.ext
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [hv₀, Submodule.coe_add, map_add, hv₀, coe_ρSym_apply, map_binarySubst, hv₀, hy g h, smul_add,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, coe_ρSym_apply,
      ← map_smul]
  · rw [hv₀, Submodule.coe_smul]

end Denominators

section Coordinates

variable (K : Type) [Field K] [CharZero K]

noncomputable def bK : Module.Basis (Module.Basis.ofVectorSpaceIndex ℚ K) ℚ K := Module.Basis.ofVectorSpace ℚ K

abbrev IK : Type := Module.Basis.ofVectorSpaceIndex ℚ K

noncomputable def crd (i : IK K) : K →+ ℚ where
  toFun x := (bK K).repr x i
  map_zero' := by simp
  map_add' x y := by simp

theorem crd_apply (i : IK K) (x : K) : crd K i x = (bK K).repr x i := rfl

private theorem _root_.HBSP.toAddMonoidHom_apply' {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (x : R) :
    φ.toAddMonoidHom x = φ x := rfl

p2m_alias "P2MW.S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top.HBSP.toAddMonoidHom_apply'" "HBSP.toAddMonoidHom_apply'"
open Classical in
theorem crd_smul_basis (i j : IK K) (q : ℚ) : crd K j (q • bK K i) = if i = j then q else 0 := by
  rw [crd_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem eq_zero_of_forall_crd (x : K) (h : ∀ i, crd K i x = 0) : x = 0 := by
  have : (bK K).repr x = 0 := Finsupp.ext fun i => h i
  exact (bK K).repr.map_eq_zero_iff.mp this

variable {K}
variable {N n : ℕ}

noncomputable def coordZ (i : IK K) (z : ↥(coeffCocycles (ρSym K N n))) : ↥(coeffCocycles (ρSym ℚ N n)) :=
  ⟨cmap (crd K i) z, cmap_mem_coeffCocycles _ z.2⟩

noncomputable def extZ (y : ↥(coeffCocycles (ρSym ℚ N n))) : ↥(coeffCocycles (ρSym K N n)) :=
  ⟨cmap (algebraMap ℚ K).toAddMonoidHom y, cmap_mem_coeffCocycles _ y.2⟩

noncomputable def extZint (K : Type) [Field K] (z₀ : ↥(coeffCocycles (ρSym ℤ N n))) : ↥(coeffCocycles (ρSym K N n)) :=
  ⟨cmap (Int.castRingHom K).toAddMonoidHom z₀, cmap_mem_coeffCocycles _ z₀.2⟩

open Classical in

theorem crd_coeff_sum_smul_extZ (s : Finset (IK K)) (y : IK K → ↥(coeffCocycles (ρSym ℚ N n)))
    (j : IK K) (g : Gamma0 N) (m : Fin 2 →₀ ℕ) :
    crd K j (coeff m (((∑ i ∈ s, bK K i • extZ (y i) : ↥(coeffCocycles (ρSym K N n))) :
      Gamma0 N → ↥(BinaryForm K n)) g : MvPolynomial (Fin 2) K)) =
      if j ∈ s then coeff m (((y j : Gamma0 N → ↥(BinaryForm ℚ n)) g : ↥(BinaryForm ℚ n)) : MvPolynomial (Fin 2) ℚ)
        else 0 := by
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, coeff_sum, coeff_smul,
    map_sum]
  have hterm : ∀ i, crd K j (bK K i • coeff m (((extZ (y i) : ↥(coeffCocycles (ρSym K N n))) :
      Gamma0 N → ↥(BinaryForm K n)) g : MvPolynomial (Fin 2) K)) =
      if i = j then coeff m (((y i : Gamma0 N → ↥(BinaryForm ℚ n)) g : ↥(BinaryForm ℚ n)) : MvPolynomial (Fin 2) ℚ)
        else 0 := by
    intro i
    change crd K j (bK K i • coeff m (mapA (algebraMap ℚ K).toAddMonoidHom _)) = _
    rw [coeff_mapA, toAddMonoidHom_apply', smul_eq_mul, mul_comm, ← Algebra.smul_def, crd_smul_basis]
  simp only [hterm]
  rw [Finset.sum_ite_eq' s j]

end Coordinates

section Main

variable (K : Type) [Field K] [CharZero K] (n N : ℕ) [NeZero N]

def genSet : Set ↥(coeffCocycles (ρSym K N n)) :=
  {w | ∃ z : ↥(coeffCocycles (ρSym ℤ N n)), ∀ g : Gamma0 N,
    ((w : Gamma0 N → ↥(BinaryForm K n)) g : MvPolynomial (Fin 2) K) =
      map (Int.castRingHom K) (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ)}

theorem extZ_mem_span (y : ↥(coeffCocycles (ρSym ℚ N n))) :
    (extZ y : ↥(coeffCocycles (ρSym K N n))) ∈ Submodule.span K (genSet K n N) := by
  obtain ⟨d, z₀, hd, hz₀⟩ := exists_int_cocycle y
  have hmem : extZint K z₀ ∈ genSet K n N := ⟨z₀, fun g => coe_cmap_ringHom _ _ g⟩
  have heq : (extZ y : ↥(coeffCocycles (ρSym K N n))) = (d : K)⁻¹ • extZint K z₀ := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun m => ?_
    have hg := congrArg (coeff m) (hz₀ g)
    rw [coeff_map, coeff_smul, smul_eq_mul, eq_intCast] at hg
    change coeff m (mapA (algebraMap ℚ K).toAddMonoidHom _) =
      coeff m ((((d : K)⁻¹ • extZint K z₀ : ↥(coeffCocycles (ρSym K N n))) : Gamma0 N → ↥(BinaryForm K n)) g :
        MvPolynomial (Fin 2) K)
    rw [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, coeff_smul, coeff_mapA]
    change algebraMap ℚ K _ = (d : K)⁻¹ • coeff m (mapA (Int.castRingHom K).toAddMonoidHom _)
    rw [coeff_mapA, toAddMonoidHom_apply', eq_intCast, smul_eq_mul]
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have : coeff m (((y : Gamma0 N → ↥(BinaryForm ℚ n)) g : ↥(BinaryForm ℚ n)) : MvPolynomial (Fin 2) ℚ) =
        (d : ℚ)⁻¹ * ((coeff m (((z₀ : Gamma0 N → ↥(BinaryForm ℤ n)) g : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ) : ℤ) : ℚ) := by
      rw [hg, ← mul_assoc, inv_mul_cancel₀ hd', one_mul]
    rw [this, map_mul, map_inv₀, map_intCast, map_intCast]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_eq_top : Submodule.span K (genSet K n N) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro z -

  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  obtain ⟨S, hS⟩ := hΓ.out

  let I₀ : Finset (IK K) := S.biUnion fun s =>
    (((z : Gamma0 N → ↥(BinaryForm K n)) s : ↥(BinaryForm K n)) : MvPolynomial (Fin 2) K).support.biUnion
      fun m => ((bK K).repr (coeff m (((z : Gamma0 N → ↥(BinaryForm K n)) s : ↥(BinaryForm K n)) :
        MvPolynomial (Fin 2) K))).support

  have hout : ∀ j, j ∉ I₀ → (coordZ j z : ↥(coeffCocycles (ρSym ℚ N n))) = 0 := by
    intro j hj
    apply Subtype.ext
    funext g
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    refine cocycle_apply_eq_zero_of_closure (ρSym ℚ N n) (coordZ j z) S (fun s hs => ?_) g hg
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun m => ?_
    change coeff m (mapA (crd K j) _) = 0
    rw [coeff_mapA, crd_apply]
    by_contra hne
    apply hj
    refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_biUnion.mpr ⟨m, ?_, Finsupp.mem_support_iff.mpr hne⟩⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hne
    rw [h0, map_zero, Finsupp.zero_apply]

  have hrec : z = ∑ i ∈ I₀, bK K i • extZ (coordZ i z) := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun m => ?_
    apply sub_eq_zero.mp
    apply eq_zero_of_forall_crd K
    intro j
    rw [map_sub, crd_coeff_sum_smul_extZ, sub_eq_zero]
    split_ifs with hj
    · rfl
    · have h := hout j hj
      have hg : coeff m ((((coordZ j z : ↥(coeffCocycles (ρSym ℚ N n))) : Gamma0 N → ↥(BinaryForm ℚ n)) g :
          ↥(BinaryForm ℚ n)) : MvPolynomial (Fin 2) ℚ) = 0 := by
        rw [h]; rfl
      change coeff m (mapA (crd K j) _) = 0 at hg
      rw [coeff_mapA] at hg
      exact hg
  rw [hrec]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (extZ_mem_span K n N _)

end Main

end HBSP
p2m_reactivate "P2MW.S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top.HBSP"

theorem solution (K : Type) [Field K] [CharZero K]
    (n N : ℕ) [NeZero N] :
    Submodule.span K
      {w : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)) |
        ∃ z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          ∀ g : CongruenceSubgroup.Gamma0 N,
            ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g : MvPolynomial (Fin 2) K) =
              MvPolynomial.map (Int.castRingHom K)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))} = ⊤ :=
  HBSP.span_eq_top K n N

end S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top
end P2MW
export P2MW.S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top (solution)
