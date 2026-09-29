-- Prove2me | solution 1 for HeckeEis.exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5b6221e3-ffb9-5328-bd69-4235520a4fb2

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_nuThree_prime
import Theorems.Thm_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
import Theorems.Thm_ModularCurve_natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree
import Theorems.Thm_HeckeEis_binaryFormRepSL_neg_one_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two

set_option autoImplicit false

open scoped MatrixGroups

namespace LevelThreeTorsionFree

open ModularCurve

private theorem nuThree_eq_zero_of_dvd (q N : ℕ) [NeZero q] (hqN : q ∣ N) (hνq : nuThree q = 0) : nuThree N = 0 := by
  have hempty : IsEmpty {x : ZMod q // x ^ 2 + x + 1 = 0} := by
    rcases Nat.card_eq_zero.mp hνq with h | h
    · exact h
    · exact absurd h (not_infinite_iff_finite.mpr inferInstance)
  unfold nuThree
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun x => hempty.false ⟨ZMod.castHom hqN (ZMod q) x.1, ?_⟩⟩
  have h := congrArg (ZMod.castHom hqN (ZMod q)) x.2
  rw [map_add, map_add, map_pow, map_one, map_zero] at h
  exact h

private theorem nuThree_eq_zero_of_exists_prime_dvd_mod_three_eq_two (N : ℕ)
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) : nuThree N = 0 := by
  obtain ⟨q, hq, hqN, hq2⟩ := hε
  have hq3 : q ≠ 3 := by
    rintro rfl
    norm_num at hq2
  have hνq : nuThree q = 0 := by
    rw [nuThree_prime hq hq3]
    simp [hq2]
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact nuThree_eq_zero_of_dvd q N hqN hνq

end LevelThreeTorsionFree

namespace D43Aux3Input

private theorem st_smul_ne_self (N : ℕ) [NeZero N] (h3 : ModularCurve.nuThree N = 0) :
    ∀ x : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N,
      (ModularGroup.S * ModularGroup.T) • x ≠ x := by
  intro x hx
  have hcard := ModularCurve.natCard_fixedPoints_ST_cosets_Gamma0_eq_nuThree N
  rw [h3] at hcard
  exact (Nat.card_ne_zero.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩) hcard

private theorem conj_st_inv_notMem (N : ℕ) [NeZero N] (h3 : ModularCurve.nuThree N = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    g⁻¹ * (ModularGroup.S * ModularGroup.T)⁻¹ * g ∉ CongruenceSubgroup.Gamma0 N := by
  intro hmem
  apply st_smul_ne_self N h3 (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N)
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]

  simpa [smul_eq_mul, mul_inv_rev, mul_assoc] using hmem

private theorem conj_st_notMem (N : ℕ) [NeZero N] (h3 : ModularCurve.nuThree N = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    g⁻¹ * (ModularGroup.S * ModularGroup.T) * g ∉ CongruenceSubgroup.Gamma0 N := by
  intro hmem
  apply conj_st_inv_notMem N h3 g
  have h := (CongruenceSubgroup.Gamma0 N).inv_mem hmem
  simpa [mul_inv_rev, mul_assoc] using h

private theorem st_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = -1 := by
  decide

private theorem neg_one_mem (N : ℕ) : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_neg]

private theorem conj_st_sq_notMem (N : ℕ) [NeZero N] (h3 : ModularCurve.nuThree N = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    g⁻¹ * (ModularGroup.S * ModularGroup.T) ^ 2 * g ∉ CongruenceSubgroup.Gamma0 N := by
  intro hmem
  apply conj_st_inv_notMem N h3 g

  have hsplit : g⁻¹ * (ModularGroup.S * ModularGroup.T) ^ 2 * g =
      (g⁻¹ * (-1) * g) * (g⁻¹ * (ModularGroup.S * ModularGroup.T)⁻¹ * g) := by
    rw [← st_pow_three]
    generalize ModularGroup.S * ModularGroup.T = w
    group

  have hc : g⁻¹ * (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈ CongruenceSubgroup.Gamma0 N := by
    rw [mul_neg, mul_one, neg_mul, inv_mul_cancel]; exact neg_one_mem N
  rw [hsplit] at hmem
  exact (CongruenceSubgroup.Gamma0 N).mul_mem_cancel_left hc |>.mp hmem

private theorem conj_st_notMem_of_heps (N : ℕ) [NeZero N] (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    g⁻¹ * (ModularGroup.S * ModularGroup.T) * g ∉ CongruenceSubgroup.Gamma0 N :=
  conj_st_notMem N (LevelThreeTorsionFree.nuThree_eq_zero_of_exists_prime_dvd_mod_three_eq_two N hε) g

private theorem st_smul_ne_self_of_heps (N : ℕ) [NeZero N] (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) :
    ∀ x : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N,
      (ModularGroup.S * ModularGroup.T) • x ≠ x :=
  st_smul_ne_self N (LevelThreeTorsionFree.nuThree_eq_zero_of_exists_prime_dvd_mod_three_eq_two N hε)

end D43Aux3Input

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL binaryFormRepSL_apply_coe coeffCocycles mem_coeffCocycles_iff coeffCoboundaries mem_coeffCoboundaries_iff existsUnique_coeffCocycles_sl2z_apply_S_ST_eq binaryFormRepSL_neg_one_apply"
p2m_open "HeckeEis"

namespace CosetInduction

section General

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {G : Type*} [Group G] (H : Subgroup G) (ρ : Representation K G V)

private noncomputable def cosetRep : Representation K G (G ⧸ H → V) where
  toFun g :=
    { toFun := fun f x => ρ g (f (g⁻¹ • x))
      map_add' := fun f f' => funext fun x => by simp only [Pi.add_apply, map_add]
      map_smul' := fun c f => funext fun x => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }
  map_one' := LinearMap.ext fun f => funext fun x => by
    simp only [map_one, inv_one, one_smul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
  map_mul' g g' := LinearMap.ext fun f => funext fun x => by
    simp only [map_mul, mul_inv_rev, mul_smul, LinearMap.coe_mk, AddHom.coe_mk,
      Module.End.mul_apply]

private theorem cosetRep_apply (g : G) (f : G ⧸ H → V) (x : G ⧸ H) :
    cosetRep H ρ g f x = ρ g (f (g⁻¹ • x)) :=
  rfl

private theorem smul_mk_eq (g a : G) :
    g • (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk (g * a) := by
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul]

private theorem inv_smul_mk_one (γ : H) :
    (γ : G)⁻¹ • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
  rw [smul_mk_eq, mul_one]
  exact QuotientGroup.eq.mpr (by simpa only [inv_inv, mul_one] using γ.2)

private noncomputable def sec (x : G ⧸ H) : G := by
  classical exact if x = (QuotientGroup.mk 1 : G ⧸ H) then 1 else Quotient.out x

private theorem mk_sec (x : G ⧸ H) : (QuotientGroup.mk (sec H x) : G ⧸ H) = x := by
  classical
  unfold sec
  split_ifs with h
  · exact h.symm
  · exact QuotientGroup.out_eq' x

private theorem sec_mk_one : sec H (QuotientGroup.mk 1 : G ⧸ H) = 1 := by
  classical
  unfold sec
  rw [if_pos rfl]

private theorem sec_inv_mul_mul_sec_mem (g : G) (x : G ⧸ H) :
    (sec H x)⁻¹ * g * sec H (g⁻¹ • x) ∈ H := by
  rw [mul_assoc]
  refine QuotientGroup.eq.mp ?_
  rw [mk_sec, ← smul_mk_eq, mk_sec, smul_inv_smul]

private noncomputable def tr (g : G) (x : G ⧸ H) : H :=
  ⟨(sec H x)⁻¹ * g * sec H (g⁻¹ • x), sec_inv_mul_mul_sec_mem H g x⟩

private theorem coe_tr (g : G) (x : G ⧸ H) :
    ((tr H g x : H) : G) = (sec H x)⁻¹ * g * sec H (g⁻¹ • x) :=
  rfl

private theorem sec_mul_tr (g : G) (x : G ⧸ H) :
    sec H x * (tr H g x : G) = g * sec H (g⁻¹ • x) := by
  rw [coe_tr, mul_assoc, mul_inv_cancel_left]

private theorem tr_mul (g g' : G) (x : G ⧸ H) :
    tr H (g * g') x = tr H g x * tr H g' (g⁻¹ • x) := by
  refine Subtype.ext ?_
  simp only [coe_tr, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

private theorem tr_coe_mk_one (γ : H) :
    tr H (γ : G) (QuotientGroup.mk 1 : G ⧸ H) = γ := by
  refine Subtype.ext ?_
  rw [coe_tr, inv_smul_mk_one, sec_mk_one, inv_one, one_mul, mul_one]

private noncomputable def toIndFun (z : H → V) (g : G) : G ⧸ H → V :=
  fun x => ρ (sec H x) (z (tr H g x))

private theorem toIndFun_mem (z : ↥(coeffCocycles (ρ.comp H.subtype))) :
    toIndFun H ρ z ∈ coeffCocycles (cosetRep H ρ) := by
  rw [mem_coeffCocycles_iff]
  intro g g'
  funext x
  have hz := (mem_coeffCocycles_iff _ _).mp z.2 (tr H g x) (tr H g' (g⁻¹ • x))
  rw [Pi.add_apply, cosetRep_apply]
  show ρ (sec H x) ((z : H → V) (tr H (g * g') x)) =
    ρ (sec H x) ((z : H → V) (tr H g x)) +
      ρ g (ρ (sec H (g⁻¹ • x)) ((z : H → V) (tr H g' (g⁻¹ • x))))
  rw [tr_mul, hz, map_add, MonoidHom.comp_apply, Subgroup.subtype_apply,
    ← Module.End.mul_apply (ρ (sec H x)), ← map_mul, sec_mul_tr, map_mul,
    Module.End.mul_apply]

private def ofIndFun (Z : G → G ⧸ H → V) (γ : H) : V :=
  Z γ (QuotientGroup.mk 1)

private theorem ofIndFun_mem (Z : ↥(coeffCocycles (cosetRep H ρ))) :
    ofIndFun H Z ∈ coeffCocycles (ρ.comp H.subtype) := by
  rw [mem_coeffCocycles_iff]
  intro γ δ
  have hZ := congrFun ((mem_coeffCocycles_iff _ _).mp Z.2 γ δ) (QuotientGroup.mk 1)
  rw [Pi.add_apply, cosetRep_apply, inv_smul_mk_one] at hZ
  simpa only [ofIndFun, Subgroup.coe_mul, MonoidHom.comp_apply, Subgroup.subtype_apply] using hZ

private noncomputable def toInd :
    ↥(coeffCocycles (ρ.comp H.subtype)) →ₗ[K] ↥(coeffCocycles (cosetRep H ρ)) where
  toFun z := ⟨toIndFun H ρ z, toIndFun_mem H ρ z⟩
  map_add' z z' := Subtype.ext (funext fun g => funext fun x => by simp [toIndFun])
  map_smul' c z := Subtype.ext (funext fun g => funext fun x => by simp [toIndFun])

private def ofInd :
    ↥(coeffCocycles (cosetRep H ρ)) →ₗ[K] ↥(coeffCocycles (ρ.comp H.subtype)) where
  toFun Z := ⟨ofIndFun H Z, ofIndFun_mem H ρ Z⟩
  map_add' Z Z' := Subtype.ext (funext fun γ => by simp [ofIndFun])
  map_smul' c Z := Subtype.ext (funext fun γ => by simp [ofIndFun])

private theorem ofInd_apply (Z : ↥(coeffCocycles (cosetRep H ρ))) (γ : H) :
    (ofInd H ρ Z : H → V) γ = (Z : G → G ⧸ H → V) γ (QuotientGroup.mk 1) :=
  rfl

private theorem toInd_apply (z : ↥(coeffCocycles (ρ.comp H.subtype))) (g : G) (x : G ⧸ H) :
    (toInd H ρ z : G → G ⧸ H → V) g x = ρ (sec H x) ((z : H → V) (tr H g x)) :=
  rfl

private theorem ofInd_toInd (z : ↥(coeffCocycles (ρ.comp H.subtype))) :
    ofInd H ρ (toInd H ρ z) = z := by
  refine Subtype.ext (funext fun γ => ?_)
  rw [ofInd_apply, toInd_apply, sec_mk_one, map_one, Module.End.one_apply, tr_coe_mk_one]

omit [AddCommGroup V] in

private theorem ofIndFun_comp {V' : Type*} (φ : V → V') (Z : G → G ⧸ H → V) (γ : H) :
    ofIndFun H (fun g x => φ (Z g x)) γ = φ (ofIndFun H Z γ) :=
  rfl

end General

end CosetInduction
end HeckeEis
end

namespace D43Aux3W

section Forms

variable (K : Type*) [CommRing K] (n : ℕ)

private theorem map_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.map (Int.castRingHom K) (HeckeEis.binarySubst ℤ M p)
      = HeckeEis.binarySubst K M (MvPolynomial.map (Int.castRingHom K) p) := by
  have key : (MvPolynomial.map (Int.castRingHom K)).comp (HeckeEis.binarySubst ℤ M).toRingHom
      = (HeckeEis.binarySubst K M).toRingHom.comp (MvPolynomial.map (Int.castRingHom K)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [HeckeEis.binarySubst_C, MvPolynomial.map_C]
    · simp [HeckeEis.binarySubst_X, MvPolynomial.map_X, MvPolynomial.map_C, eq_intCast]
  exact congrArg (fun φ => φ p) key

private noncomputable def redForm : ↥(HeckeEis.BinaryForm ℤ n) →+ ↥(HeckeEis.BinaryForm K n) where
  toFun q := ⟨MvPolynomial.map (Int.castRingHom K) (q : MvPolynomial (Fin 2) ℤ),
    (MvPolynomial.mem_homogeneousSubmodule ..).mpr
      (((MvPolynomial.mem_homogeneousSubmodule ..).mp q.2).map (Int.castRingHom K))⟩
  map_zero' := Subtype.ext (by simp)
  map_add' q q' := Subtype.ext (by simp)

private theorem redForm_coe (q : ↥(HeckeEis.BinaryForm ℤ n)) :
    ((redForm K n q : ↥(HeckeEis.BinaryForm K n)) : MvPolynomial (Fin 2) K)
      = MvPolynomial.map (Int.castRingHom K) (q : MvPolynomial (Fin 2) ℤ) :=
  rfl

private theorem redForm_rep (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (q : ↥(HeckeEis.BinaryForm ℤ n)) :
    redForm K n (HeckeEis.binaryFormRepSL ℤ n g q) = HeckeEis.binaryFormRepSL K n g (redForm K n q) := by
  apply Subtype.ext
  rw [redForm_coe, HeckeEis.binaryFormRepSL_apply_coe, HeckeEis.binaryFormRepSL_apply_coe, redForm_coe]
  exact map_binarySubst K _ _

private theorem span_range_redForm_eq_top : Submodule.span K (Set.range (redForm K n)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨p, hp⟩ -
  have hpn : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule ..).mp hp

  let mono : (Fin 2 →₀ ℕ) → p.support → ↥(HeckeEis.BinaryForm ℤ n) := fun _ m =>
    ⟨MvPolynomial.monomial m.1 (1 : ℤ), (MvPolynomial.mem_homogeneousSubmodule ..).mpr
      (MvPolynomial.isHomogeneous_monomial (1 : ℤ) (by
        by_contra hdeg
        exact (MvPolynomial.mem_support_iff.mp m.2) (hpn.coeff_eq_zero hdeg)))⟩

  have hsum : (⟨p, hp⟩ : ↥(HeckeEis.BinaryForm K n))
      = ∑ m : p.support, MvPolynomial.coeff m.1 p • redForm K n (mono 0 m) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, redForm_coe, MvPolynomial.map_monomial, map_one]

    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [← Finset.sum_coe_sort p.support]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mono, Submodule.coe_smul, redForm_coe, Submodule.coe_mk, MvPolynomial.map_monomial, map_one,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsum]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨mono 0 m, rfl⟩)

end Forms

section Induced

variable (K : Type*) [CommRing K] (n : ℕ) {X : Type*}

private noncomputable def redW : (X → ↥(HeckeEis.BinaryForm ℤ n)) →+ (X → ↥(HeckeEis.BinaryForm K n)) :=
  AddMonoidHom.pi fun x => (redForm K n).comp (Pi.evalAddMonoidHom _ x)

private theorem redW_apply (f : X → ↥(HeckeEis.BinaryForm ℤ n)) (x : X) : redW K n f x = redForm K n (f x) :=
  rfl

private theorem redW_induced [MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) X]
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f : X → ↥(HeckeEis.BinaryForm ℤ n)) :
    redW K n (fun x => HeckeEis.binaryFormRepSL ℤ n g (f (g⁻¹ • x)))
      = fun x => HeckeEis.binaryFormRepSL K n g (redW K n f (g⁻¹ • x)) :=
  funext fun x => by rw [redW_apply, redW_apply, redForm_rep]

private theorem span_range_redW_eq_top [Finite X] : Submodule.span K (Set.range (redW K n (X := X))) = ⊤ := by
  classical
  cases nonempty_fintype X
  rw [eq_top_iff]
  rintro f -
  rw [← Finset.univ_sum_single f]
  refine Submodule.sum_mem _ fun x _ => ?_

  have h3 : f x ∈ Submodule.span K (Set.range (redForm K n)) := by rw [span_range_redForm_eq_top]; trivial
  have hmap := Submodule.span_image (LinearMap.single K (fun _ : X => ↥(HeckeEis.BinaryForm K n)) x)
    (s := Set.range (redForm K n))
  refine Submodule.span_mono ?_ (hmap ▸ Submodule.mem_map_of_mem h3)
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact ⟨Pi.single x q, funext fun y => by by_cases hy : y = x <;> simp [redW_apply, hy, Pi.single_apply]⟩

private theorem redW_cosetRep (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (f : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ H → ↥(HeckeEis.BinaryForm ℤ n)) :
    redW K n (HeckeEis.CosetInduction.cosetRep H (HeckeEis.binaryFormRepSL ℤ n) g f)
      = HeckeEis.CosetInduction.cosetRep H (HeckeEis.binaryFormRepSL K n) g (redW K n f) :=

  redW_induced K n g f

private theorem span_range_redW_cosets_eq_top (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    [Finite (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ H)] :
    Submodule.span K (Set.range (redW K n (X := Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ H))) = ⊤ :=
  span_range_redW_eq_top K n

end Induced

end D43Aux3W

namespace D43Aux3Gen

section Gen

variable (K : Type*) [CommRing K] (n : ℕ) (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
  [Finite (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ H)]

private theorem hgen_redW (v : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ H → ↥(HeckeEis.BinaryForm K n)) :
    ∃ (m : ℕ) (c : Fin m → K)
      (u : Fin m → (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ H → ↥(HeckeEis.BinaryForm ℤ n))),
      v = ∑ i, c i • D43Aux3W.redW K n (u i) := by
  classical
  have hv : v ∈ Submodule.span K (Set.range (D43Aux3W.redW K n)) := by
    rw [D43Aux3W.span_range_redW_cosets_eq_top K n H]; trivial
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv

  refine ⟨l.support.card, fun i => l (l.support.equivFin.symm i), fun i => (l.support.equivFin.symm i : _), ?_⟩
  rw [← hl, Finsupp.sum, ← Finset.sum_coe_sort l.support]
  exact (Fintype.sum_equiv l.support.equivFin.symm _ _ fun i => rfl).symm

end Gen

end D43Aux3Gen

namespace CocycleLiftSL2

p2m_open "HeckeEis P2MW.S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two.HeckeEis P2MW.S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two.HeckeEis.CosetInduction ModularGroup"

private theorem S_mul_S_eq_neg_one : (S : SL(2, ℤ)) * S = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact S_mul_S_eq

private theorem ST_cube_eq_neg_one : (S * T) * (S * T) * (S * T) = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T]
  decide

section Generic

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K SL(2, ℤ) V)

private theorem apply_one_eq_zero (z : SL(2, ℤ) → V) (hz : z ∈ coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [one_mul, map_one, Module.End.one_apply] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

private theorem apply_neg_one_eq_zero (t : K) (ht : t * 2 = 1) (hneg : ρ (-1) = 1) (z : SL(2, ℤ) → V)
    (hz : z ∈ coeffCocycles ρ) : z (-1) = 0 := by
  have h := hz (-1) (-1)
  rw [neg_one_mul, neg_neg, apply_one_eq_zero ρ z hz, hneg, Module.End.one_apply] at h
  have h2 : (2 : K) • z (-1) = 0 := by
    rw [two_smul]
    exact h.symm
  calc z (-1) = (t * 2) • z (-1) := by rw [ht, one_smul]
    _ = t • ((2 : K) • z (-1)) := by rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

private theorem apply_S_norm (z : SL(2, ℤ) → V) (hz : z ∈ coeffCocycles ρ) : z S + ρ S (z S) = z (-1) := by
  rw [← hz S S, S_mul_S_eq_neg_one]

private theorem apply_ST_norm (z : SL(2, ℤ) → V) (hz : z ∈ coeffCocycles ρ) :
    z (S * T) + ρ (S * T) (z (S * T)) + ρ (S * T) (ρ (S * T) (z (S * T))) = z (-1) := by
  have h1 := hz ((S * T) * (S * T)) (S * T)
  rw [ST_cube_eq_neg_one, hz (S * T) (S * T), map_mul ρ (S * T) (S * T), Module.End.mul_apply] at h1
  exact h1.symm

private theorem S_norm_of_sub (hneg : ρ (-1) = 1) (u : V) : (u - ρ S u) + ρ S (u - ρ S u) = 0 := by
  have h : ρ S (ρ S u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, S_mul_S_eq_neg_one, hneg, Module.End.one_apply]
  rw [map_sub, h]
  abel

private theorem ST_norm_of_sub (hneg : ρ (-1) = 1) (u : V) :
    (u - ρ (S * T) u) + ρ (S * T) (u - ρ (S * T) u) + ρ (S * T) (ρ (S * T) (u - ρ (S * T) u)) = 0 := by
  have h : ρ (S * T) (ρ (S * T) (ρ (S * T) u)) = u := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ST_cube_eq_neg_one, hneg,
      Module.End.one_apply]
  simp only [map_sub]
  rw [h]
  abel

private theorem ST_norm_zero : (0 : V) + ρ (S * T) 0 + ρ (S * T) (ρ (S * T) 0) = 0 := by
  simp

private theorem S_norm_zero : (0 : V) + ρ S 0 = 0 := by
  simp

private noncomputable def ofPair (x y : V) (hx : x + ρ S x = 0)
    (hy : y + ρ (S * T) y + ρ (S * T) (ρ (S * T) y) = 0) : ↥(coeffCocycles ρ) :=
  (existsUnique_coeffCocycles_sl2z_apply_S_ST_eq K V ρ x y hx hy).exists.choose

private theorem ofPair_spec (x y : V) (hx : x + ρ S x = 0) (hy : y + ρ (S * T) y + ρ (S * T) (ρ (S * T) y) = 0) :
    (ofPair ρ x y hx hy : SL(2, ℤ) → V) S = x ∧ (ofPair ρ x y hx hy : SL(2, ℤ) → V) (S * T) = y :=
  (existsUnique_coeffCocycles_sl2z_apply_S_ST_eq K V ρ x y hx hy).exists.choose_spec

private theorem eq_of_apply_S_eq_of_apply_ST_eq (t : K) (ht : t * 2 = 1) (hneg : ρ (-1) = 1)
    (z w : ↥(coeffCocycles ρ)) (hS : (z : SL(2, ℤ) → V) S = (w : SL(2, ℤ) → V) S)
    (hST : (z : SL(2, ℤ) → V) (S * T) = (w : SL(2, ℤ) → V) (S * T)) : z = w := by
  have hx : (z : SL(2, ℤ) → V) S + ρ S ((z : SL(2, ℤ) → V) S) = 0 := by
    rw [apply_S_norm ρ z z.2, apply_neg_one_eq_zero ρ t ht hneg z z.2]
  have hy : (z : SL(2, ℤ) → V) (S * T) + ρ (S * T) ((z : SL(2, ℤ) → V) (S * T))
      + ρ (S * T) (ρ (S * T) ((z : SL(2, ℤ) → V) (S * T))) = 0 := by
    rw [apply_ST_norm ρ z z.2, apply_neg_one_eq_zero ρ t ht hneg z z.2]
  exact (existsUnique_coeffCocycles_sl2z_apply_S_ST_eq K V ρ _ _ hx hy).unique ⟨rfl, rfl⟩ ⟨hS.symm, hST.symm⟩

end Generic

section Lift

variable {R : Type*} [CommRing R] {VR : Type*} [AddCommGroup VR] [Module R VR] (ρR : Representation R SL(2, ℤ) VR)
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K SL(2, ℤ) V)
variable (r : VR →+ V)

private def pushCocycle (hr : ∀ (g : SL(2, ℤ)) (v : VR), r (ρR g v) = ρ g (r v))
    (Y : ↥(coeffCocycles ρR)) : ↥(coeffCocycles ρ) :=
  ⟨fun g => r ((Y : SL(2, ℤ) → VR) g), fun g h => by
    show r ((Y : SL(2, ℤ) → VR) (g * h)) = r ((Y : SL(2, ℤ) → VR) g) + ρ g (r ((Y : SL(2, ℤ) → VR) h))
    rw [Y.2 g h, map_add, hr]⟩

private theorem pushCocycle_apply (hr : ∀ (g : SL(2, ℤ)) (v : VR), r (ρR g v) = ρ g (r v))
    (Y : ↥(coeffCocycles ρR)) (g : SL(2, ℤ)) :
    (pushCocycle ρR ρ r hr Y : SL(2, ℤ) → V) g = r ((Y : SL(2, ℤ) → VR) g) :=
  rfl

private theorem sum_S_part (hr : ∀ (g : SL(2, ℤ)) (v : VR), r (ρR g v) = ρ g (r v))
    (t : K) (ht : t * 2 = 1) (x : V) (hx : x + ρ S x = 0) {m : ℕ} (c : Fin m → K) (u : Fin m → VR)
    (hxu : x = ∑ i, c i • r (u i)) :
    ∑ i, (t * c i) • r (u i - ρR S (u i)) = x := by
  have hSx : ρ S x = -x := eq_neg_of_add_eq_zero_right hx
  have h1 : ∀ i, r (u i - ρR S (u i)) = r (u i) - ρ S (r (u i)) := fun i => by rw [map_sub, hr]
  have h2 : ∑ i, (t * c i) • r (u i - ρR S (u i)) = t • x - t • ρ S x := by
    simp only [h1, hxu, mul_smul, smul_sub, map_sum, map_smul, Finset.smul_sum, Finset.sum_sub_distrib]
  rw [h2, hSx, smul_neg, sub_neg_eq_add, ← two_smul K (t • x), smul_smul, mul_comm, ht, one_smul]

private theorem sum_ST_part (hr : ∀ (g : SL(2, ℤ)) (v : VR), r (ρR g v) = ρ g (r v))
    (y y₁ : V) (hy : y = y₁ - ρ (S * T) y₁) {m : ℕ} (d : Fin m → K) (v : Fin m → VR)
    (hyv : y₁ = ∑ j, d j • r (v j)) :
    ∑ j, d j • r (v j - ρR (S * T) (v j)) = y := by
  have h1 : ∀ j, r (v j - ρR (S * T) (v j)) = r (v j) - ρ (S * T) (r (v j)) := fun j => by rw [map_sub, hr]
  rw [hy, hyv]
  simp only [h1, smul_sub, map_sum, map_smul, Finset.sum_sub_distrib]

private theorem exists_eq_sum_smul_push (hr : ∀ (g : SL(2, ℤ)) (v : VR), r (ρR g v) = ρ g (r v))
    (t : K) (ht : t * 2 = 1) (hnegR : ρR (-1) = 1) (hneg : ρ (-1) = 1)
    (hgen : ∀ v : V, ∃ (m : ℕ) (c : Fin m → K) (u : Fin m → VR), v = ∑ i, c i • r (u i))
    (hfree : ∀ v : V, v + ρ (S * T) v + ρ (S * T) (ρ (S * T) v) = 0 → ∃ v₁ : V, v = v₁ - ρ (S * T) v₁)
    (z : ↥(coeffCocycles ρ)) :
    ∃ (m : ℕ) (c : Fin m → K) (y : Fin m → ↥(coeffCocycles ρR)), ∀ g : SL(2, ℤ),
      (z : SL(2, ℤ) → V) g = ∑ i, c i • r ((y i : SL(2, ℤ) → VR) g) := by
  set x : V := (z : SL(2, ℤ) → V) S with hxdef
  set yv : V := (z : SL(2, ℤ) → V) (S * T) with hydef
  have hx : x + ρ S x = 0 := by
    rw [hxdef, apply_S_norm ρ z z.2, apply_neg_one_eq_zero ρ t ht hneg z z.2]
  have hy : yv + ρ (S * T) yv + ρ (S * T) (ρ (S * T) yv) = 0 := by
    rw [hydef, apply_ST_norm ρ z z.2, apply_neg_one_eq_zero ρ t ht hneg z z.2]
  obtain ⟨m₁, c, u, hxu⟩ := hgen x
  obtain ⟨y₁, hy₁⟩ := hfree yv hy
  obtain ⟨m₂, d, v, hyv⟩ := hgen y₁
  let Y₁ : Fin m₁ → ↥(coeffCocycles ρR) := fun i =>
    ofPair ρR (u i - ρR S (u i)) 0 (S_norm_of_sub ρR hnegR (u i)) (ST_norm_zero ρR)
  let Y₂ : Fin m₂ → ↥(coeffCocycles ρR) := fun j =>
    ofPair ρR 0 (v j - ρR (S * T) (v j)) (S_norm_zero ρR) (ST_norm_of_sub ρR hnegR (v j))
  let W : ↥(coeffCocycles ρ) :=
    (∑ i, (t * c i) • pushCocycle ρR ρ r hr (Y₁ i)) + ∑ j, d j • pushCocycle ρR ρ r hr (Y₂ j)
  have hW : ∀ g : SL(2, ℤ), (W : SL(2, ℤ) → V) g =
      ∑ i, (t * c i) • r ((Y₁ i : SL(2, ℤ) → VR) g) + ∑ j, d j • r ((Y₂ j : SL(2, ℤ) → VR) g) := by
    intro g
    simp only [W, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.add_apply,
      Pi.smul_apply, pushCocycle_apply]
  have hWS : (W : SL(2, ℤ) → V) S = x := by
    rw [hW]
    have e1 : ∀ i, (Y₁ i : SL(2, ℤ) → VR) S = u i - ρR S (u i) := fun i => (ofPair_spec ρR _ _ _ _).1
    have e2 : ∀ j, (Y₂ j : SL(2, ℤ) → VR) S = 0 := fun j => (ofPair_spec ρR _ _ _ _).1
    simp only [e1, e2, map_zero, smul_zero, Finset.sum_const_zero, add_zero]
    exact sum_S_part ρR ρ r hr t ht x hx c u hxu
  have hWST : (W : SL(2, ℤ) → V) (S * T) = yv := by
    rw [hW]
    have e1 : ∀ i, (Y₁ i : SL(2, ℤ) → VR) (S * T) = 0 := fun i => (ofPair_spec ρR _ _ _ _).2
    have e2 : ∀ j, (Y₂ j : SL(2, ℤ) → VR) (S * T) = v j - ρR (S * T) (v j) := fun j => (ofPair_spec ρR _ _ _ _).2
    simp only [e1, e2, map_zero, smul_zero, Finset.sum_const_zero, zero_add]
    exact sum_ST_part ρR ρ r hr yv y₁ hy₁ d v hyv
  have hzW : z = W := eq_of_apply_S_eq_of_apply_ST_eq ρ t ht hneg z W hWS.symm hWST.symm
  refine ⟨m₁ + m₂, Fin.append (fun i => t * c i) d, Fin.append Y₁ Y₂, fun g => ?_⟩
  rw [hzW, hW g, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

end Lift

section Exactness

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (H : Subgroup SL(2, ℤ)) (ρ : Representation K SL(2, ℤ) V)

private theorem neg_one_smul_coset (hH : (-1 : SL(2, ℤ)) ∈ H) (x : SL(2, ℤ) ⧸ H) : (-1 : SL(2, ℤ)) • x = x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, neg_one_mul, ← mul_neg_one, QuotientGroup.mk_mul_of_mem a hH]

private theorem st_cube_smul (hH : (-1 : SL(2, ℤ)) ∈ H) (x : SL(2, ℤ) ⧸ H) :
    (S * T) • (S * T) • (S * T) • x = x := by
  rw [← mul_smul, ← mul_smul, ST_cube_eq_neg_one, neg_one_smul_coset H hH]

private theorem st_inv_smul (hH : (-1 : SL(2, ℤ)) ∈ H) (x : SL(2, ℤ) ⧸ H) :
    (S * T)⁻¹ • x = (S * T) • (S * T) • x := by
  conv_lhs => rw [← st_cube_smul H hH x]
  rw [inv_smul_smul]

private theorem st_sq_smul_ne (hH : (-1 : SL(2, ℤ)) ∈ H) (hfix : ∀ x : SL(2, ℤ) ⧸ H, (S * T) • x ≠ x)
    (x : SL(2, ℤ) ⧸ H) : (S * T) • (S * T) • x ≠ x := by
  intro h
  apply hfix x
  have h' := congrArg (fun y => (S * T) • y) h
  beta_reduce at h'
  rw [st_cube_smul H hH] at h'
  exact h'.symm

private theorem zpow_smul_cases (hH : (-1 : SL(2, ℤ)) ∈ H) (m : ℤ) (y : SL(2, ℤ) ⧸ H) :
    (S * T) ^ m • y = y ∨ (S * T) ^ m • y = (S * T) • y ∨ (S * T) ^ m • y = (S * T) • (S * T) • y := by
  induction m using Int.induction_on generalizing y with
  | zero => left; rw [zpow_zero, one_smul]
  | succ m ih =>
    rw [zpow_add_one, mul_smul]
    rcases ih ((S * T) • y) with h | h | h
    · right; left; exact h
    · right; right; exact h
    · left; rw [h, st_cube_smul H hH]
  | pred m ih =>
    rw [zpow_sub_one, mul_smul, st_inv_smul H hH]
    rcases ih ((S * T) • (S * T) • y) with h | h | h
    · right; right; exact h
    · left; rw [h, st_cube_smul H hH]
    · right; left; rw [h, st_cube_smul H hH]

private noncomputable def rep (x : SL(2, ℤ) ⧸ H) : SL(2, ℤ) ⧸ H :=
  (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers (S * T)) (SL(2, ℤ) ⧸ H)) x).out

private theorem rep_st_smul (x : SL(2, ℤ) ⧸ H) : rep H ((S * T) • x) = rep H x := by
  unfold rep
  congr 1
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨⟨S * T, Subgroup.mem_zpowers _⟩, rfl⟩

private theorem rep_rep (x : SL(2, ℤ) ⧸ H) : rep H (rep H x) = rep H x := by
  unfold rep
  rw [Quotient.out_eq]

private theorem rep_cases (hH : (-1 : SL(2, ℤ)) ∈ H) (x : SL(2, ℤ) ⧸ H) :
    x = rep H x ∨ x = (S * T) • rep H x ∨ x = (S * T) • (S * T) • rep H x := by
  have hrel : (MulAction.orbitRel (Subgroup.zpowers (S * T)) (SL(2, ℤ) ⧸ H)) (rep H x) x := by
    unfold rep
    exact Quotient.mk_out x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨⟨g, hg⟩, hgx⟩ := hrel
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  change (S * T) ^ m • x = rep H x at hgx
  have key := zpow_smul_cases H hH (-m) (rep H x)
  have hx : x = (S * T) ^ (-m) • rep H x := by
    rw [← hgx, ← mul_smul, zpow_neg, inv_mul_cancel, one_smul]
  rw [← hx] at key
  exact key

private theorem rep_st_inv_smul (hH : (-1 : SL(2, ℤ)) ∈ H) (x : SL(2, ℤ) ⧸ H) : rep H ((S * T)⁻¹ • x) = rep H x := by
  rw [st_inv_smul H hH, rep_st_smul, rep_st_smul]

private theorem exists_eq_sub_cosetRep_st_of_norm_eq_zero (hH : (-1 : SL(2, ℤ)) ∈ H)
    (hfix : ∀ x : SL(2, ℤ) ⧸ H, (S * T) • x ≠ x) (f : SL(2, ℤ) ⧸ H → V)
    (hf : f + cosetRep H ρ (S * T) f + cosetRep H ρ (S * T) (cosetRep H ρ (S * T) f) = 0) :
    ∃ f₁ : SL(2, ℤ) ⧸ H → V, f = f₁ - cosetRep H ρ (S * T) f₁ := by
  classical
  refine ⟨fun x => if x = rep H x then 0 else if x = (S * T) • rep H x then f x
    else f x + ρ (S * T) (f ((S * T) • rep H x)), ?_⟩
  funext x
  simp only [Pi.sub_apply, cosetRep_apply]
  obtain ⟨r, hr0, hxr⟩ : ∃ r : SL(2, ℤ) ⧸ H, rep H r = r ∧
      (x = r ∨ x = (S * T) • r ∨ x = (S * T) • (S * T) • r) :=
    ⟨rep H x, rep_rep H x, rep_cases H hH x⟩
  have n1 : (S * T) • r ≠ r := hfix r
  have n2 : (S * T) • (S * T) • r ≠ r := st_sq_smul_ne H hH hfix r
  have n3 : (S * T) • (S * T) • r ≠ (S * T) • r := hfix ((S * T) • r)
  have hfr := congrFun hf r
  simp only [Pi.add_apply, cosetRep_apply, Pi.zero_apply, st_inv_smul H hH, st_cube_smul H hH] at hfr
  rcases hxr with rfl | rfl | rfl
  · simp only [st_inv_smul H hH, rep_st_smul, hr0, n2, n3, if_true, if_false]
    rw [zero_sub, map_add, add_assoc] at *
    exact eq_neg_of_add_eq_zero_left hfr
  · simp only [inv_smul_smul, rep_st_smul, hr0, n1, if_true, if_false]
    rw [map_zero, sub_zero]
  · simp only [inv_smul_smul, rep_st_smul, hr0, n1, n2, n3, if_true, if_false]
    rw [add_sub_cancel_right]

end Exactness

section Glue

variable (H : Subgroup SL(2, ℤ))

private theorem cosetRep_neg_one {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K SL(2, ℤ) V) (hH : (-1 : SL(2, ℤ)) ∈ H) (hρ : ρ (-1) = 1) : cosetRep H ρ (-1) = 1 := by
  ext f x
  rw [cosetRep_apply, hρ, Module.End.one_apply, Module.End.one_apply, inv_neg, inv_one, neg_one_smul_coset H hH]

private theorem two_mul_two_eq_one (F : Type*) [Field F] [CharP F 3] : (2 : F) * 2 = 1 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  linear_combination h3

private theorem exists_eq_sum_smul_map_of_reduction (F : Type*) [Field F] [CharP F 3] (n : ℕ)
    (hH : (-1 : SL(2, ℤ)) ∈ H) (hfix : ∀ x : SL(2, ℤ) ⧸ H, (S * T) • x ≠ x)
    (hnegZ : binaryFormRepSL ℤ n (-1) = 1) (hnegF : binaryFormRepSL F n (-1) = 1)
    (r : (SL(2, ℤ) ⧸ H → ↥(BinaryForm ℤ n)) →+ (SL(2, ℤ) ⧸ H → ↥(BinaryForm F n)))
    (hr_coe : ∀ (u : SL(2, ℤ) ⧸ H → ↥(BinaryForm ℤ n)) (x : SL(2, ℤ) ⧸ H),
      ((r u x : ↥(BinaryForm F n)) : MvPolynomial (Fin 2) F)
        = MvPolynomial.map (Int.castRingHom F) ((u x : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ))
    (hr : ∀ (g : SL(2, ℤ)) (u : SL(2, ℤ) ⧸ H → ↥(BinaryForm ℤ n)),
      r (cosetRep H (binaryFormRepSL ℤ n) g u) = cosetRep H (binaryFormRepSL F n) g (r u))
    (hgen : ∀ v : SL(2, ℤ) ⧸ H → ↥(BinaryForm F n),
      ∃ (m : ℕ) (c : Fin m → F) (u : Fin m → (SL(2, ℤ) ⧸ H → ↥(BinaryForm ℤ n))), v = ∑ i, c i • r (u i))
    (Z : ↥(coeffCocycles (cosetRep H (binaryFormRepSL F n)))) :
    ∃ (m : ℕ) (c : Fin m → F) (Y : Fin m → ↥(coeffCocycles (cosetRep H (binaryFormRepSL ℤ n)))),
      ∀ (g : SL(2, ℤ)) (x : SL(2, ℤ) ⧸ H),
        (((Z : SL(2, ℤ) → SL(2, ℤ) ⧸ H → ↥(BinaryForm F n)) g x : ↥(BinaryForm F n)) : MvPolynomial (Fin 2) F)
          = ∑ i, c i • MvPolynomial.map (Int.castRingHom F)
              (((Y i : SL(2, ℤ) → SL(2, ℤ) ⧸ H → ↥(BinaryForm ℤ n)) g x : ↥(BinaryForm ℤ n)) :
                MvPolynomial (Fin 2) ℤ) := by
  obtain ⟨m, c, Y, hY⟩ := exists_eq_sum_smul_push (cosetRep H (binaryFormRepSL ℤ n))
    (cosetRep H (binaryFormRepSL F n)) r hr 2 (two_mul_two_eq_one F) (cosetRep_neg_one H _ hH hnegZ)
    (cosetRep_neg_one H _ hH hnegF) hgen (exists_eq_sub_cosetRep_st_of_norm_eq_zero H (binaryFormRepSL F n) hH hfix) Z
  refine ⟨m, c, Y, fun g x => ?_⟩
  have h := congrFun (hY g) x
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply] at h
  rw [h, Submodule.coe_sum]
  simp only [Submodule.coe_smul, hr_coe]

end Glue

end CocycleLiftSL2

namespace H1primeSol

private theorem mem_coeffCoboundaries_of_central_neg {G : Type*} [Group G] {K : Type*} [CommRing K]
    [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (c : G) (hc : ∀ g : G, c * g = g * c) (hneg : ∀ v : V, ρ c v = -v)
    {z : G → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) : z ∈ HeckeEis.coeffCoboundaries ρ := by
  rw [HeckeEis.mem_coeffCoboundaries_iff]
  refine ⟨-((⅟(2 : K)) • z c), ?_⟩
  funext g
  have h1 : z (g * c) = z g + ρ g (z c) := hz g c
  have h2 : z (c * g) = z c + ρ c (z g) := hz c g
  rw [hc g, hneg] at h2
  have h4 : z g + ρ g (z c) = z c + -z g := h1.symm.trans h2
  have h3 : (2 : K) • z g = z c - ρ g (z c) := by
    rw [two_smul, eq_sub_iff_add_eq, add_assoc, h4]
    abel
  rw [map_neg, map_smul, neg_sub_neg, ← smul_sub, ← h3, invOf_smul_smul]

private theorem two_ne_zero_of_charP_three (F : Type) [Field F] [CharP F 3] : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  have h3 : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff F 3 2).mp h'
  omega

private theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem]

private theorem mem_coeffCoboundaries_of_odd (F : Type) [Field F] [CharP F 3] (n N : ℕ) (hn : Odd n)
    (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n))
    (hz : z ∈ HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    z ∈ HeckeEis.coeffCoboundaries
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype) := by
  letI : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero_of_charP_three F)
  refine mem_coeffCoboundaries_of_central_neg _ ⟨-1, neg_one_mem_Gamma0 N⟩ ?_ ?_ hz
  · intro g
    apply Subtype.ext
    show (-1 : SL(2, ℤ)) * (g : SL(2, ℤ)) = (g : SL(2, ℤ)) * (-1)
    rw [neg_one_mul, mul_neg_one]
  · intro P
    show HeckeEis.binaryFormRepSL F n (-1) P = -P
    rw [HeckeEis.binaryFormRepSL_neg_one_apply, hn.neg_one_pow]

    first
      | exact neg_one_smul F P
      | exact Subtype.ext (neg_one_smul F (P : MvPolynomial (Fin 2) F))

private theorem binaryFormRepSL_neg_one_eq_one (K : Type*) [CommRing K] (n : ℕ) (hn : Even n) :
    HeckeEis.binaryFormRepSL K n (-1) = 1 := by
  refine LinearMap.ext fun P => ?_
  rw [HeckeEis.binaryFormRepSL_neg_one_apply, hn.neg_one_pow, one_smul, Module.End.one_apply]

private theorem p4_concrete (F : Type) [Field F] [CharP F 3] (n N : ℕ) [NeZero N]
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (hnegZ : HeckeEis.binaryFormRepSL ℤ n (-1) = 1) (hnegF : HeckeEis.binaryFormRepSL F n (-1) = 1)
    (Z : ↥(HeckeEis.coeffCocycles
      (HeckeEis.CosetInduction.cosetRep (CongruenceSubgroup.Gamma0 N) (HeckeEis.binaryFormRepSL F n)))) :
    ∃ (m : ℕ) (c : Fin m → F) (Y : Fin m → ↥(HeckeEis.coeffCocycles
        (HeckeEis.CosetInduction.cosetRep (CongruenceSubgroup.Gamma0 N) (HeckeEis.binaryFormRepSL ℤ n)))),
      ∀ (g : SL(2, ℤ)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
        (((Z : SL(2, ℤ) → SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g x :
            ↥(HeckeEis.BinaryForm F n)) : MvPolynomial (Fin 2) F)
          = ∑ i, c i • MvPolynomial.map (Int.castRingHom F)
              (((Y i : SL(2, ℤ) → SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g x :
                  ↥(HeckeEis.BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ) :=
  CocycleLiftSL2.exists_eq_sum_smul_map_of_reduction (CongruenceSubgroup.Gamma0 N) F n
    (D43Aux3Input.neg_one_mem N) (D43Aux3Input.st_smul_ne_self_of_heps N hε) hnegZ hnegF
    (D43Aux3W.redW F n) (fun _ _ => rfl) (D43Aux3W.redW_cosetRep F n (CongruenceSubgroup.Gamma0 N))
    (D43Aux3Gen.hgen_redW F n (CongruenceSubgroup.Gamma0 N)) Z

end H1primeSol

theorem solution
    (F : Type) [Field F] [CharP F 3] (n N : ℕ) [NeZero N] (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (z : ↥(HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ (m : ℕ) (c : Fin m → F)
      (y : Fin m → ↥(HeckeEis.coeffCocycles
        ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
      (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)),
      w ∈ HeckeEis.coeffCoboundaries
          ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype) ∧
        ∀ g : CongruenceSubgroup.Gamma0 N,
          (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g : MvPolynomial (Fin 2) F)) =
            (∑ i : Fin m, c i • MvPolynomial.map (Int.castRingHom F)
                (((y i : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g :
                  MvPolynomial (Fin 2) ℤ))) +
              ((w g : ↥(HeckeEis.BinaryForm F n)) : MvPolynomial (Fin 2) F) := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, c, Y, hY⟩ := H1primeSol.p4_concrete F n N hε
      (H1primeSol.binaryFormRepSL_neg_one_eq_one ℤ n hn) (H1primeSol.binaryFormRepSL_neg_one_eq_one F n hn)
      (HeckeEis.CosetInduction.toInd (CongruenceSubgroup.Gamma0 N) (HeckeEis.binaryFormRepSL F n) z)
    refine ⟨m, c,
      fun i => HeckeEis.CosetInduction.ofInd (CongruenceSubgroup.Gamma0 N) (HeckeEis.binaryFormRepSL ℤ n) (Y i),
      0, Submodule.zero_mem _, fun g => ?_⟩
    rw [← HeckeEis.CosetInduction.ofInd_toInd (CongruenceSubgroup.Gamma0 N) (HeckeEis.binaryFormRepSL F n) z,
      HeckeEis.CosetInduction.ofInd_apply, hY]
    simp [HeckeEis.CosetInduction.ofInd_apply]
  · refine ⟨0, Fin.elim0, Fin.elim0, (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)),
      H1primeSol.mem_coeffCoboundaries_of_odd F n N hn _ z.2, ?_⟩
    intro g
    simp

#print axioms solution

end S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two (solution)
