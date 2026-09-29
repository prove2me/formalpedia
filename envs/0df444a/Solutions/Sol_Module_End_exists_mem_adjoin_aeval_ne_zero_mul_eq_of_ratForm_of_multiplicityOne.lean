-- Prove2me | solution 1 for Module.End.exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c315775a-e392-5b27-8ea7-0c37b56a3764

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne

set_option autoImplicit false

open Polynomial

namespace RatGoodGen

section Setup

variable {L V σ : Type*} [Field L] [CharZero L] [AddCommGroup V] [Module L V]
  [Module ℚ V] [IsScalarTower ℚ L V]

theorem finite_VQ [FiniteDimensional L V] (VQ : Submodule ℚ V)
    (hli : ∀ (n : ℕ) (v : Fin n → V), (∀ i, v i ∈ VQ) →
      LinearIndependent ℚ v → LinearIndependent L v) :
    Module.Finite ℚ VQ := by
  have hr : Module.rank ℚ VQ ≤ (Module.finrank L V : ℕ) := by
    apply rank_le
    intro s hs
    let e := s.equivFin
    have h1 : LinearIndependent ℚ (fun i : Fin s.card => ((e.symm i : s) : VQ)) :=
      hs.comp _ e.symm.injective
    have h2 : LinearIndependent ℚ (fun i : Fin s.card => (((e.symm i : s) : VQ) : V)) :=
      h1.map' VQ.subtype (Submodule.ker_subtype VQ)
    have h3 := hli _ _ (fun i => ((e.symm i : s) : VQ).2) h2
    simpa using h3.fintype_card_le_finrank
  exact Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)

variable (VQ : Submodule ℚ V) (ρ : MvPolynomial σ ℤ →+* Module.End L V)
  (hrat : ∀ (i : σ) (v : V), v ∈ VQ → ρ (MvPolynomial.X i) v ∈ VQ)

include hrat in
theorem mapsTo (f : MvPolynomial σ ℤ) : ∀ v ∈ VQ, ρ f v ∈ VQ := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro v hv
    rw [eq_intCast MvPolynomial.C a, map_intCast, Module.End.intCast_apply]
    exact zsmul_mem hv a
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hp v hv) (hq v hv)
  | mul_X p i hp =>
    intro v hv
    rw [map_mul, Module.End.mul_apply]
    exact hp _ (hrat i v hv)

noncomputable def resQ (f : MvPolynomial σ ℤ) : Module.End ℚ VQ :=
  ((ρ f).restrictScalars ℚ).restrict (fun v hv => mapsTo VQ ρ hrat f v hv)

theorem coe_resQ (f : MvPolynomial σ ℤ) (w : VQ) : ((resQ VQ ρ hrat f w : VQ) : V) = ρ f w := rfl

noncomputable def rhoQ : MvPolynomial σ ℤ →+* Module.End ℚ VQ where
  toFun := resQ VQ ρ hrat
  map_one' := LinearMap.ext fun w => Subtype.ext (by
    rw [coe_resQ, map_one]; rfl)
  map_mul' f g := LinearMap.ext fun w => Subtype.ext (by
    rw [coe_resQ, map_mul]; rfl)
  map_zero' := LinearMap.ext fun w => Subtype.ext (by
    rw [coe_resQ, map_zero]; rfl)
  map_add' f g := LinearMap.ext fun w => Subtype.ext (by
    rw [coe_resQ, map_add]; rfl)

theorem coe_rhoQ (f : MvPolynomial σ ℤ) (w : VQ) : ((rhoQ VQ ρ hrat f w : VQ) : V) = ρ f w := rfl

variable (G : Set σ) (lam : σ → L)

noncomputable def CQ : Subalgebra ℚ (Module.End ℚ VQ) :=
  Algebra.adjoin ℚ (Set.range fun g : G => rhoQ VQ ρ hrat (MvPolynomial.X (g : σ)))

scoped instance isMulCommutative_CQ : IsMulCommutative (CQ VQ ρ hrat G) :=
  Algebra.isMulCommutative_adjoin ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

noncomputable def CV : Subalgebra ℚ (Module.End L V) :=
  Algebra.adjoin ℚ (Set.range fun g : G => ρ (MvPolynomial.X (g : σ)))

scoped instance isMulCommutative_CV : IsMulCommutative (CV ρ G) :=
  Algebra.isMulCommutative_adjoin ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative

noncomputable def evQ : MvPolynomial G ℚ →ₐ[ℚ] CQ VQ ρ hrat G :=
  MvPolynomial.aeval fun g : G =>
    (⟨rhoQ VQ ρ hrat (MvPolynomial.X (g : σ)), Algebra.subset_adjoin (Set.mem_range_self g)⟩ : CQ VQ ρ hrat G)

noncomputable def evV : MvPolynomial G ℚ →ₐ[ℚ] Module.End L V :=
  (CV ρ G).val.comp (MvPolynomial.aeval fun g : G =>
    (⟨ρ (MvPolynomial.X (g : σ)), Algebra.subset_adjoin (Set.mem_range_self g)⟩ : CV ρ G))

noncomputable def chi : MvPolynomial G ℚ →ₐ[ℚ] L :=
  MvPolynomial.aeval fun g : G => lam (g : σ)

set_option synthInstance.maxHeartbeats 1600000 in
theorem evQ_X (g : G) :
    ((evQ VQ ρ hrat G (MvPolynomial.X g) : CQ VQ ρ hrat G) : Module.End ℚ VQ) =
      rhoQ VQ ρ hrat (MvPolynomial.X (g : σ)) := by
  rw [evQ, MvPolynomial.aeval_X]

set_option synthInstance.maxHeartbeats 1600000 in
theorem evV_X (g : G) : evV ρ G (MvPolynomial.X g) = ρ (MvPolynomial.X (g : σ)) := by
  rw [evV, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl

theorem chi_X (g : G) : chi G lam (MvPolynomial.X g) = lam (g : σ) :=
  MvPolynomial.aeval_X _ g

theorem evQ_C (a : ℚ) :
    ((evQ VQ ρ hrat G (MvPolynomial.C a) : CQ VQ ρ hrat G) : Module.End ℚ VQ) =
      algebraMap ℚ (Module.End ℚ VQ) a := by
  rw [show (MvPolynomial.C a : MvPolynomial G ℚ) = algebraMap ℚ _ a from rfl, AlgHom.commutes]
  rfl

theorem evV_C (a : ℚ) : evV ρ G (MvPolynomial.C a) = algebraMap ℚ (Module.End L V) a := by
  rw [show (MvPolynomial.C a : MvPolynomial G ℚ) = algebraMap ℚ _ a from rfl, AlgHom.commutes]

theorem chi_C (a : ℚ) : chi G lam (MvPolynomial.C a) = algebraMap ℚ L a := by
  rw [show (MvPolynomial.C a : MvPolynomial G ℚ) = algebraMap ℚ _ a from rfl, AlgHom.commutes]

theorem evQ_surjective : Function.Surjective (evQ VQ ρ hrat G) := by
  intro y
  suffices h : ∃ q, ((evQ VQ ρ hrat G q : CQ VQ ρ hrat G) : Module.End ℚ VQ) = y by
    obtain ⟨q, hq⟩ := h; exact ⟨q, Subtype.ext hq⟩
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨MvPolynomial.X g, evQ_X VQ ρ hrat G g⟩
  | algebraMap r => exact ⟨MvPolynomial.C r, evQ_C VQ ρ hrat G r⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx; obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, Subalgebra.coe_add, hp, hq]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx; obtain ⟨q, hq⟩ := hy
    exact ⟨p * q, by rw [map_mul, Subalgebra.coe_mul, hp, hq]⟩

theorem coe_evQ (q : MvPolynomial G ℚ) (w : VQ) :
    ((((evQ VQ ρ hrat G q : CQ VQ ρ hrat G) : Module.End ℚ VQ) w : VQ) : V) = evV ρ G q (w : V) := by
  induction q using MvPolynomial.induction_on generalizing w with
  | C a =>
    rw [evQ_C, evV_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
  | add p q hp hq =>
    rw [map_add, map_add, Subalgebra.coe_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add,
      hp, hq]
  | mul_X p g hp =>
    rw [map_mul, map_mul, Subalgebra.coe_mul, evQ_X, evV_X, Module.End.mul_apply, Module.End.mul_apply,
      hp, coe_rhoQ]

theorem evV_map (q : MvPolynomial G ℤ) :
    evV ρ G (MvPolynomial.map (Int.castRingHom ℚ) q) = ρ (MvPolynomial.rename ((↑) : G → σ) q) := by
  have key : ((evV ρ G).toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ)))
      = ρ.comp (MvPolynomial.rename ((↑) : G → σ)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun g => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, eq_intCast, map_intCast,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.rename_X]
      exact evV_X ρ G g
  exact RingHom.congr_fun key q

theorem chi_map (q : MvPolynomial G ℤ) :
    chi G lam (MvPolynomial.map (Int.castRingHom ℚ) q) =
      MvPolynomial.aeval lam (MvPolynomial.rename ((↑) : G → σ) q) := by
  rw [MvPolynomial.aeval_rename, chi, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  rfl

theorem rhoQ_rename (q : MvPolynomial G ℤ) :
    rhoQ VQ ρ hrat (MvPolynomial.rename ((↑) : G → σ) q) =
      ((evQ VQ ρ hrat G (MvPolynomial.map (Int.castRingHom ℚ) q) : CQ VQ ρ hrat G) : Module.End ℚ VQ) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [coe_rhoQ, coe_evQ, evV_map]

theorem commute_evQ_rhoQ (q : MvPolynomial G ℚ) (t : MvPolynomial σ ℤ) :
    Commute ((evQ VQ ρ hrat G q : CQ VQ ρ hrat G) : Module.End ℚ VQ) (rhoQ VQ ρ hrat t) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [evQ_C]
    exact Algebra.commute_algebraMap_left a _
  | add p q hp hq => rw [map_add, Subalgebra.coe_add]; exact hp.add_left hq
  | mul_X p g hp =>
    rw [map_mul, Subalgebra.coe_mul, evQ_X]
    refine hp.mul_left ?_
    show rhoQ VQ ρ hrat _ * rhoQ VQ ρ hrat t = rhoQ VQ ρ hrat t * rhoQ VQ ρ hrat _
    rw [← map_mul, ← map_mul, mul_comm]

theorem coe_mul_comm (x y : CQ VQ ρ hrat G) :
    (x : Module.End ℚ VQ) * (y : Module.End ℚ VQ) = (y : Module.End ℚ VQ) * (x : Module.End ℚ VQ) := by
  rw [← Subalgebra.coe_mul, mul_comm, Subalgebra.coe_mul]

theorem coe_aeval_of_coe {A : Module.End ℚ VQ} {B : Module.End L V}
    (hAB : ∀ w : VQ, ((A w : VQ) : V) = B (w : V)) (r : ℚ[X]) (w : VQ) :
    ((Polynomial.aeval A r w : VQ) : V) = Polynomial.aeval B (r.map (algebraMap ℚ L)) (w : V) := by
  induction r using Polynomial.induction_on' generalizing w with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Submodule.coe_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, Submodule.coe_smul, algebraMap_smul]
    congr 1
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hAB]

end Setup

section Denominators

theorem exists_int_multiple {G : Type*} (s₀ : MvPolynomial G ℚ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ sZ : MvPolynomial G ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) sZ = MvPolynomial.C (N : ℚ) * s₀ := by
  classical

  let N : ℕ := ∏ m ∈ s₀.support, (s₀.coeff m).den
  have hNpos : 0 < N := Finset.prod_pos fun m _ => (s₀.coeff m).den_pos
  have hdvd : ∀ m ∈ s₀.support, ((s₀.coeff m).den : ℤ) ∣ (N : ℤ) := fun m hm => by
    have : (s₀.coeff m).den ∣ N := Finset.dvd_prod_of_mem (fun m => (s₀.coeff m).den) hm
    exact_mod_cast this

  have hint : ∀ m ∈ s₀.support, ∃ z : ℤ, (z : ℚ) = (N : ℚ) * s₀.coeff m := fun m hm => by
    obtain ⟨k, hk⟩ := hdvd m hm
    refine ⟨k * (s₀.coeff m).num, ?_⟩
    have h1 : (N : ℚ) = ((s₀.coeff m).den : ℚ) * (k : ℚ) := by exact_mod_cast hk
    have h2 : s₀.coeff m * ((s₀.coeff m).den : ℚ) = ((s₀.coeff m).num : ℚ) := Rat.mul_den_eq_num _
    rw [h1, Int.cast_mul]
    calc (k : ℚ) * ((s₀.coeff m).num : ℚ) = (k : ℚ) * (s₀.coeff m * ((s₀.coeff m).den : ℚ)) := by
          rw [h2]
      _ = ((s₀.coeff m).den : ℚ) * (k : ℚ) * s₀.coeff m := by ring
  choose! z hz using hint
  refine ⟨(N : ℤ), by exact_mod_cast hNpos.ne', ∑ m ∈ s₀.support, MvPolynomial.monomial m (z m), ?_⟩
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum s₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.map_monomial, eq_intCast, hz m hm, MvPolynomial.C_mul_monomial, Int.cast_natCast]

end Denominators

section Main

variable {L V σ : Type*} [Field L] [CharZero L] [AddCommGroup V] [Module L V]
  [Module ℚ V] [IsScalarTower ℚ L V]

theorem linearIndependent_of_poly {W : Type*} [AddCommGroup W] [Module ℚ W]
    (h : Module.End ℚ W) (w : W) (n : ℕ)
    (hpoly : ∀ r : ℚ[X], r.degree < n → Polynomial.aeval h r w = 0 → r = 0) :
    LinearIndependent ℚ (fun j : Fin n => (h ^ (j : ℕ)) w) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let r : ℚ[X] := ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  have hr : Polynomial.aeval h r w = 0 := by
    have : Polynomial.aeval h r = ∑ i : Fin n, c i • h ^ (i : ℕ) := by
      simp only [r, map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Algebra.smul_def]
    rw [this, LinearMap.sum_apply]
    simpa only [LinearMap.smul_apply] using hc
  have hr0 : r = 0 := hpoly r (Polynomial.degree_sum_fin_lt c) hr
  have : r.coeff j = c j := by
    simp only [r, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (Fin.ext h.symm))) (by simp)]
    simp
  rw [← this, hr0, Polynomial.coeff_zero]

theorem coeff_sum_fin {n : ℕ} (b : Fin n → ℚ) (j : Fin n) :
    (∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)).coeff j = b j := by
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (Fin.ext h.symm))) (by simp)]
  simp

open scoped IsMulCommutative

set_option maxHeartbeats 16000000 in

theorem engine [FiniteDimensional L V]
    (VQ : Submodule ℚ V)
    (hli : ∀ (n : ℕ) (v : Fin n → V), (∀ i, v i ∈ VQ) →
      LinearIndependent ℚ v → LinearIndependent L v)
    (hspan : Submodule.span L (VQ : Set V) = ⊤)
    (ρ : MvPolynomial σ ℤ →+* Module.End L V)
    (hrat : ∀ (i : σ) (v : V), v ∈ VQ → ρ (MvPolynomial.X i) v ∈ VQ)
    (G : Set σ)
    (hss : ∀ i ∈ G, ∃ P : Polynomial ℚ, P.Separable ∧
      Polynomial.aeval (ρ (MvPolynomial.X i)) (P.map (algebraMap ℚ L)) = 0)
    (lam : σ → L) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (heig : ∀ i ∈ G, ρ (MvPolynomial.X i) v₀ = lam i • v₀)
    (hmult : ∀ w : V, (∀ i ∈ G, ρ (MvPolynomial.X i) w = lam i • w) → ∃ c : L, w = c • v₀)
    (t : MvPolynomial σ ℤ) :
    ∃ s ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
      ∃ u ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
        MvPolynomial.aeval lam s ≠ 0 ∧ ρ s * ρ t = ρ u := by
  classical
  haveI hfin : Module.Finite ℚ VQ := finite_VQ VQ hli

  let T' : Subalgebra ℚ (Module.End ℚ VQ) := CQ VQ ρ hrat G
  let E := Module.End ℚ VQ
  let ρQ := rhoQ VQ ρ hrat
  let eQ : MvPolynomial G ℚ →ₐ[ℚ] T' := evQ VQ ρ hrat G
  let eV := evV ρ G
  let χ := chi G lam
  have hsurj : Function.Surjective eQ := evQ_surjective VQ ρ hrat G
  have hcoe : ∀ q (w : VQ), ((((eQ q : T') : E) w : VQ) : V) = eV q (w : V) := coe_evQ VQ ρ hrat G
  have hcommT : ∀ x y : T', (x : E) * (y : E) = (y : E) * (x : E) := coe_mul_comm VQ ρ hrat G

  have hC2 : ∀ q, eV q v₀ = χ q • v₀ := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      show evV ρ G (MvPolynomial.C a) v₀ = chi G lam (MvPolynomial.C a) • v₀
      rw [evV_C, chi_C, Module.algebraMap_end_apply, algebraMap_smul]
    | add p q hp hq =>
      show evV ρ G (p + q) v₀ = chi G lam (p + q) • v₀
      rw [map_add, map_add, LinearMap.add_apply, add_smul]
      exact congrArg₂ (· + ·) hp hq
    | mul_X p g hp =>
      show evV ρ G (p * MvPolynomial.X g) v₀ = chi G lam (p * MvPolynomial.X g) • v₀
      rw [map_mul, map_mul, evV_X, chi_X, Module.End.mul_apply, heig _ g.2, map_smul,
        show evV ρ G p v₀ = chi G lam p • v₀ from hp, smul_smul, mul_comm]

  have hC4 : ∀ q, eQ q = 0 → χ q = 0 := by
    intro q hq
    have h1 : eV q = 0 := by
      refine LinearMap.ext_on hspan (fun v hv => ?_)
      rw [LinearMap.zero_apply]
      have := hcoe q ⟨v, hv⟩
      rw [hq] at this
      exact this.symm.trans rfl
    have h2 : χ q • v₀ = 0 := by rw [← hC2, show eV q = 0 from h1, LinearMap.zero_apply]
    exact (smul_eq_zero.1 h2).resolve_right hv₀

  haveI : Module.Finite ℚ T' :=
    Module.Finite.of_injective (Subalgebra.val T').toLinearMap Subtype.val_injective
  haveI : IsArtinianRing T' := IsArtinianRing.of_finite ℚ T'
  have hgenss : ∀ g : G, (ρQ (MvPolynomial.X (g : σ))).IsSemisimple := by
    intro g
    obtain ⟨P, hPsep, hP⟩ := hss g g.2
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hPsep.squarefree ?_
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [coe_aeval_of_coe VQ (fun w => coe_rhoQ VQ ρ hrat _ w) P w, hP]
    rfl
  have hss' : ∀ q, ((eQ q : T') : E).IsSemisimple := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      show (((evQ VQ ρ hrat G (MvPolynomial.C a)) : T') : E).IsSemisimple
      rw [evQ_C, Algebra.algebraMap_eq_smul_one]
      exact Module.End.IsSemisimple_smul a Module.End.isSemisimple_id
    | add p q hp hq =>
      show (((evQ VQ ρ hrat G (p + q)) : T') : E).IsSemisimple
      rw [map_add, Subalgebra.coe_add]
      exact Module.End.IsSemisimple.add_of_commute (hcommT _ _) hp hq
    | mul_X p g hp =>
      show (((evQ VQ ρ hrat G (p * MvPolynomial.X g)) : T') : E).IsSemisimple
      rw [map_mul, Subalgebra.coe_mul, evQ_X]
      exact Module.End.IsSemisimple.mul_of_commute
        (commute_evQ_rhoQ VQ ρ hrat G p _) hp (hgenss g)
  have hallss : ∀ x : T', (x : E).IsSemisimple := fun x => by
    obtain ⟨q, rfl⟩ := hsurj x; exact hss' q
  haveI : IsReduced T' := ⟨by
    intro x hx
    have h1 : IsNilpotent (x : E) := by
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, by rw [← Subalgebra.coe_pow, hn]; rfl⟩
    exact Subtype.ext (Module.End.eq_zero_of_isNilpotent_isSemisimple h1 (hallss x))⟩
  have hSS : IsSemisimpleRing T' := IsArtinianRing.isSemisimpleRing_of_isReduced T'

  have hker : ∀ a ∈ RingHom.ker eQ, χ a = 0 := fun a ha => hC4 a (RingHom.mem_ker.1 ha)
  let equ : (MvPolynomial G ℚ ⧸ RingHom.ker eQ) ≃ₐ[ℚ] T' := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let χbar : (MvPolynomial G ℚ ⧸ RingHom.ker eQ) →ₐ[ℚ] L := Ideal.Quotient.liftₐ _ χ hker
  let χ' : T' →ₐ[ℚ] L := χbar.comp equ.symm.toAlgHom
  have hχ' : ∀ q, χ' (eQ q) = χ q := by
    intro q
    have h1 : equ.symm (eQ q) = Ideal.Quotient.mk _ q := by
      rw [AlgEquiv.symm_apply_eq, Ideal.quotientKerAlgEquivOfSurjective_apply]
      rfl
    show χbar (equ.symm (eQ q)) = χ q
    rw [h1]
    exact Ideal.Quotient.lift_mk _ _ _

  let I : Ideal T' := RingHom.ker χ'
  have hmemI : ∀ x : T', x ∈ I ↔ χ' x = 0 := fun x => RingHom.mem_ker
  obtain ⟨J, hIJ⟩ := hSS.toComplementedLattice.exists_isCompl I
  obtain ⟨a, ha, e, he, hae⟩ : ∃ a ∈ I, ∃ e ∈ J, a + e = 1 :=
    Submodule.mem_sup.1 (by rw [hIJ.sup_eq_top]; exact Submodule.mem_top)
  have hIe : ∀ m ∈ I, m * e = 0 := by
    intro m hm
    have h1 : m * e ∈ I ⊓ J := ⟨by rw [mul_comm]; exact Ideal.mul_mem_left I e hm,
      Ideal.mul_mem_left J m he⟩
    rw [hIJ.inf_eq_bot] at h1
    exact h1
  have hχe : χ' e = 1 := by
    have h1 : χ' a + χ' e = 1 := by rw [← map_add, hae, map_one]
    rwa [(hmemI a).1 ha, zero_add] at h1

  let Killed : VQ → Prop := fun w => ∀ m ∈ I, ((m : T') : E) w = 0
  have hKe : ∀ w : VQ, Killed (((e : T') : E) w) := fun w m hm => by
    show (((m : T') : E) * ((e : T') : E)) w = 0
    rw [← Subalgebra.coe_mul, hIe m hm]; rfl
  have hKρ : ∀ (f : MvPolynomial σ ℤ) (w : VQ), Killed w → Killed (ρQ f w) := by
    intro f w hw m hm
    obtain ⟨q, hq⟩ := hsurj m
    have h1 : ((m : T') : E) = ((evQ VQ ρ hrat G q : T') : E) := by rw [← hq]
    rw [h1, ← Module.End.mul_apply, (commute_evQ_rhoQ VQ ρ hrat G q f).eq, Module.End.mul_apply,
      ← h1, hw m hm, map_zero]

  let F₀ : Subalgebra ℚ L := χ'.range
  haveI : Module.Finite ℚ F₀ :=
    Module.Finite.of_surjective χ'.rangeRestrict.toLinearMap (AlgHom.rangeRestrict_surjective χ')
  have hF₀alg : ∀ x ∈ F₀, IsAlgebraic ℚ x := fun x hx => by
    have h1 : IsIntegral ℚ (⟨x, hx⟩ : F₀) := IsIntegral.of_finite ℚ _
    exact (h1.algebraMap (B := L)).isAlgebraic
  let F₁ : IntermediateField ℚ L :=
    F₀.toIntermediateField fun x hx => Subalgebra.inv_mem_of_algebraic F₀ (x := ⟨x, hx⟩) (hF₀alg x hx)
  haveI : FiniteDimensional ℚ F₁ := (inferInstance : Module.Finite ℚ F₀)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F₁
  let β : L := (α : L)
  have hαint : IsIntegral ℚ α := IsIntegral.of_finite ℚ α
  have hβint : IsIntegral ℚ β := hαint.algebraMap

  have hinv : ∀ x : T', x ∉ I → ∃ y : T', ∀ w : VQ, Killed w → ((y : T') : E) (((x : T') : E) w) = w := by
    intro x hx
    rw [hmemI] at hx
    have h0 : (χ' x)⁻¹ ∈ F₀ := (⟨χ' x, ⟨x, rfl⟩⟩ : F₁)⁻¹.2
    obtain ⟨y, hy⟩ := h0
    have hy' : χ' y = (χ' x)⁻¹ := hy
    have hi : 1 - y * x ∈ I := by
      rw [hmemI]
      have e1 : χ' (1 - y * x) = χ' 1 - χ' (y * x) := map_sub χ' _ _
      have e2 : χ' (y * x) = χ' y * χ' x := map_mul χ' _ _
      rw [e1, e2, map_one, hy', inv_mul_cancel₀ hx, sub_self]
    refine ⟨y, fun w hw => ?_⟩
    have h2 : y * x + (1 - y * x) = (1 : T') := by abel
    have h1 : ((y * x + (1 - y * x) : T') : E) w = w := by rw [h2]; rfl
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, LinearMap.add_apply, hw _ hi, add_zero,
      Module.End.mul_apply] at h1
    exact h1

  have hF₀poly : ∀ x ∈ F₀, ∃ r : ℚ[X], x = Polynomial.aeval β r := by
    intro x hx
    have hx1 : (⟨x, hx⟩ : F₁) ∈ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by
      rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic] at hx1
    have hx2 : x ∈ Subalgebra.map F₁.val (Algebra.adjoin ℚ {α}) := ⟨⟨x, hx⟩, hx1, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.adjoin_singleton_eq_range_aeval] at hx2
    obtain ⟨r, hr⟩ := hx2
    exact ⟨r, hr.symm⟩

  obtain ⟨hβ, hhβ⟩ : ∃ hβ : T', χ' hβ = β := (α : F₀).2
  obtain ⟨qβ, hqβ⟩ := hsurj hβ
  let Hβ : Module.End L V := eV qβ
  have hHβ : ∀ w : VQ, ((((hβ : T') : E) w : VQ) : V) = Hβ (w : V) := fun w => by
    rw [← hqβ]; exact hcoe qβ w
  have hHβpow : ∀ (j : ℕ) (w : VQ), (((((hβ : T') : E) ^ j) w : VQ) : V) = (Hβ ^ j) (w : V) := by
    intro j w
    induction j generalizing w with
    | zero => rfl
    | succ j ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hHβ]

  have hcoeaeval : ∀ r : ℚ[X], ((Polynomial.aeval hβ r : T') : E) = Polynomial.aeval ((hβ : T') : E) r :=
    fun r => (Polynomial.aeval_algHom_apply T'.val hβ r).symm
  have hχ'aeval : ∀ r : ℚ[X], χ' (Polynomial.aeval hβ r) = Polynomial.aeval β r := fun r => by
    rw [← Polynomial.aeval_algHom_apply, hhβ]

  let p : ℚ[X] := minpoly ℚ β
  have hpmonic : p.Monic := minpoly.monic hβint
  let n : ℕ := p.natDegree

  have hnotI : ∀ r : ℚ[X], r ≠ 0 → r.degree < n → (Polynomial.aeval hβ r : T') ∉ I := by
    intro r hr0 hr
    have h1 : Polynomial.aeval β r ≠ 0 := fun h => by
      have := minpoly.degree_le_of_ne_zero ℚ β hr0 h
      exact absurd (this.trans_lt hr) (not_lt.2 (Polynomial.degree_eq_natDegree hpmonic.ne_zero).ge)
    rw [hmemI, hχ'aeval]; exact h1
  have hpolycrit : ∀ w : VQ, Killed w → w ≠ 0 → ∀ r : ℚ[X], r.degree < n →
      Polynomial.aeval ((hβ : T') : E) r w = 0 → r = 0 := by
    intro w hw hw0 r hr hrw
    by_contra hr0
    obtain ⟨y, hy⟩ := hinv _ (hnotI r hr0 hr)
    apply hw0
    have h3 := hy w hw
    rw [hcoeaeval, hrw, map_zero] at h3
    exact h3.symm

  let pL : L[X] := p.map (algebraMap ℚ L)
  have hpLroot : pL.IsRoot β := by
    show (p.map (algebraMap ℚ L)).IsRoot β
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]; exact minpoly.aeval ℚ β
  let Q : L[X] := pL /ₘ (Polynomial.X - Polynomial.C β)
  have hpQ : (Polynomial.X - Polynomial.C β) * Q = pL := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hpLroot
  have hQmonic : Q.Monic := Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C β)
    (by rw [hpQ]; exact hpmonic.map _)
  have hQdeg : Q.natDegree + 1 = n := by
    have h1 : pL.natDegree = n := Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective p
    have h2 := congrArg Polynomial.natDegree hpQ
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero β) hQmonic.ne_zero,
      Polynomial.natDegree_X_sub_C, h1] at h2
    omega

  have hgood : ∀ g : G, ∃ r : ℚ[X], (eQ (MvPolynomial.X g) - Polynomial.aeval hβ r : T') ∈ I ∧
      Polynomial.aeval β r = lam g := by
    intro g
    have hmem : χ' (eQ (MvPolynomial.X g)) = lam g := by
      rw [hχ']; exact chi_X G lam g
    obtain ⟨r, hr⟩ := hF₀poly (lam g) (by rw [← hmem]; exact ⟨_, rfl⟩)
    refine ⟨r, ?_, hr.symm⟩
    rw [hmemI]
    have e1 : χ' (eQ (MvPolynomial.X g) - Polynomial.aeval hβ r) = χ' (eQ (MvPolynomial.X g)) - χ' (Polynomial.aeval hβ r) :=
      map_sub χ' _ _
    rw [e1, hmem, hχ'aeval, ← hr, sub_self]
  choose rg hrgI hrg using hgood

  have hkey : ∀ w : VQ, Killed w → w ≠ 0 →
      ∃ c : L, c ≠ 0 ∧ Polynomial.aeval Hβ Q (w : V) = c • v₀ := by
    intro w hw hw0

    have h1 : Polynomial.aeval Hβ pL (w : V) = 0 := by
      have h4 : (Polynomial.aeval hβ p : T') ∈ I := by
        rw [hmemI, hχ'aeval]; exact minpoly.aeval ℚ β
      have h3 : Polynomial.aeval ((hβ : T') : E) p w = 0 := by
        have := hw _ h4
        rwa [hcoeaeval] at this
      have h2 := coe_aeval_of_coe VQ hHβ p w
      rw [h3, ZeroMemClass.coe_zero] at h2
      exact h2.symm

    have hx1 : Hβ (Polynomial.aeval Hβ Q (w : V)) = β • Polynomial.aeval Hβ Q (w : V) := by
      have h5 : (Hβ - algebraMap L _ β) (Polynomial.aeval Hβ Q (w : V)) = 0 := by
        rw [← Module.End.mul_apply, show Hβ - algebraMap L (Module.End L V) β
            = Polynomial.aeval Hβ (Polynomial.X - Polynomial.C β) by
          rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C], ← map_mul, hpQ, h1]
      rw [LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h5
      exact h5

    have hx2 : ∀ R : L[X], Polynomial.aeval Hβ R (Polynomial.aeval Hβ Q (w : V))
        = (Polynomial.eval β R) • Polynomial.aeval Hβ Q (w : V) := by
      intro R
      induction R using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add, Polynomial.eval_add, LinearMap.add_apply, hp, hq, add_smul]
      | monomial k a =>
        rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
          Module.algebraMap_end_apply, mul_smul]
        congr 1
        induction k with
        | zero => rw [pow_zero, pow_zero, one_smul]; rfl
        | succ k ih =>
          rw [pow_succ', pow_succ', Module.End.mul_apply, ih, map_smul, hx1, smul_smul, mul_comm]

    have hx3 : ∀ i ∈ G, ρ (MvPolynomial.X i) (Polynomial.aeval Hβ Q (w : V))
        = lam i • Polynomial.aeval Hβ Q (w : V) := by
      intro i hi
      let g : G := ⟨i, hi⟩

      have e1 : ρ (MvPolynomial.X i) (w : V) = Polynomial.aeval Hβ ((rg g).map (algebraMap ℚ L)) (w : V) := by
        have h2 := hw _ (hrgI g)
        rw [Subalgebra.coe_sub, LinearMap.sub_apply, sub_eq_zero, evQ_X, hcoeaeval] at h2
        have h3 := congrArg (fun z : VQ => (z : V)) h2
        rw [coe_rhoQ, coe_aeval_of_coe VQ hHβ] at h3
        exact h3

      have hcomm : Commute (ρ (MvPolynomial.X i)) Hβ := by
        show ρ (MvPolynomial.X i) * evV ρ G qβ = evV ρ G qβ * ρ (MvPolynomial.X i)
        rw [← evV_X ρ G g, ← map_mul, ← map_mul, mul_comm]
      have hcommQ : ∀ R : L[X], Commute (ρ (MvPolynomial.X i)) (Polynomial.aeval Hβ R) := by
        intro R
        induction R using Polynomial.induction_on' with
        | add p q hp hq => rw [map_add]; exact hp.add_right hq
        | monomial k a =>
          rw [Polynomial.aeval_monomial]
          exact (Algebra.commute_algebraMap_right a _).mul_right (hcomm.pow_right k)
      calc ρ (MvPolynomial.X i) (Polynomial.aeval Hβ Q (w : V))
            = Polynomial.aeval Hβ Q (ρ (MvPolynomial.X i) (w : V)) := by
            rw [← Module.End.mul_apply, (hcommQ Q).eq, Module.End.mul_apply]
        _ = Polynomial.aeval Hβ ((rg g).map (algebraMap ℚ L)) (Polynomial.aeval Hβ Q (w : V)) := by
            rw [e1, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
        _ = lam i • Polynomial.aeval Hβ Q (w : V) := by
            rw [hx2, Polynomial.eval_map_algebraMap, hrg g]

    have hLI : LinearIndependent L (fun j : Fin n => (Hβ ^ (j : ℕ)) (w : V)) := by
      have e1 : LinearIndependent ℚ (fun j : Fin n => (((hβ : T') : E) ^ (j : ℕ)) w) :=
        linearIndependent_of_poly _ w n (hpolycrit w hw hw0)
      have e2 : LinearIndependent ℚ (fun j : Fin n => (((((hβ : T') : E) ^ (j : ℕ)) w : VQ) : V)) :=
        e1.map' VQ.subtype (Submodule.ker_subtype VQ)
      have e3 := hli n _ (fun j => ((((hβ : T') : E) ^ (j : ℕ)) w).2) e2
      convert e3 using 1
      funext j
      exact (hHβpow j w).symm
    have hx0 : Polynomial.aeval Hβ Q (w : V) ≠ 0 := by
      intro hx
      have e1 : ∑ j : Fin n, Q.coeff j • (Hβ ^ (j : ℕ)) (w : V) = 0 := by
        have e2 : Polynomial.aeval Hβ Q (w : V)
            = ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j • (Hβ ^ j) (w : V) := by
          rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
          rfl
        rw [hQdeg, Finset.sum_range (fun j => Q.coeff j • (Hβ ^ j) (w : V))] at e2
        rw [← e2, hx]
      have e3 := (Fintype.linearIndependent_iff.1 hLI) (fun j => Q.coeff j) e1 ⟨n - 1, by omega⟩
      have e4 : Q.coeff (n - 1) = 1 := by
        rw [show n - 1 = Q.natDegree by omega]; exact hQmonic
      simp only at e3
      rw [e4] at e3
      exact one_ne_zero e3
    obtain ⟨c, hc⟩ := hmult _ hx3
    exact ⟨c, fun hc0 => hx0 (by rw [hc, hc0, zero_smul]), hc⟩

  have haeval : ∀ (b : Fin n → ℚ) (w : VQ),
      Polynomial.aeval ((hβ : T') : E) (∑ j : Fin n, Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)) w
        = ∑ j : Fin n, b j • (((hβ : T') : E) ^ (j : ℕ)) w := by
    intro b w
    simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, LinearMap.sum_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply]
  have hcyc : ∀ w₂ : VQ, Killed w₂ → w₂ ≠ 0 → ∀ w₁ : VQ, Killed w₁ →
      ∃ y : T', w₁ = ((y : T') : E) w₂ := by
    intro w₂ hw₂ hw₂0 w₁ hw₁
    by_cases hw₁0 : w₁ = 0
    · exact ⟨0, by rw [hw₁0, ZeroMemClass.coe_zero, LinearMap.zero_apply]⟩
    obtain ⟨c₁, hc₁, hx₁⟩ := hkey w₁ hw₁ hw₁0
    obtain ⟨c₂, hc₂, hx₂⟩ := hkey w₂ hw₂ hw₂0

    let uu : Fin n ⊕ Fin n → V :=
      Sum.elim (fun j => (Hβ ^ (j : ℕ)) (w₁ : V)) (fun j => (Hβ ^ (j : ℕ)) (w₂ : V))
    have esum : ∀ w : V, ∑ j : Fin n, Q.coeff j • (Hβ ^ (j : ℕ)) w = Polynomial.aeval Hβ Q w := by
      intro w
      rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, hQdeg,
        Finset.sum_range (fun j => (Q.coeff j • Hβ ^ j) w)]
      rfl
    have hrel : ∑ k, (Sum.elim (fun j : Fin n => c₂ * Q.coeff j) (fun j : Fin n => -(c₁ * Q.coeff j)) k) • uu k = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [uu, Sum.elim_inl, Sum.elim_inr]
      have e2 : ∑ j : Fin n, (c₂ * Q.coeff j) • (Hβ ^ (j : ℕ)) (w₁ : V)
          = c₂ • Polynomial.aeval Hβ Q (w₁ : V) := by
        rw [← esum, Finset.smul_sum]; simp_rw [mul_smul]
      have e3 : ∑ j : Fin n, (-(c₁ * Q.coeff j)) • (Hβ ^ (j : ℕ)) (w₂ : V)
          = -(c₁ • Polynomial.aeval Hβ Q (w₂ : V)) := by
        rw [← esum, Finset.smul_sum, ← Finset.sum_neg_distrib]; simp_rw [neg_smul, mul_smul]
      rw [e2, e3, hx₁, hx₂, smul_smul, smul_smul, mul_comm c₂ c₁, ← sub_eq_add_neg, sub_self]
    have hnotL : ¬ LinearIndependent L uu := by
      intro hind
      have := (Fintype.linearIndependent_iff.1 hind) _ hrel (Sum.inl ⟨n - 1, by omega⟩)
      simp only [Sum.elim_inl] at this
      rw [show n - 1 = Q.natDegree by omega, hQmonic.coeff_natDegree, mul_one] at this
      exact hc₂ this

    let uuQ : Fin n ⊕ Fin n → VQ :=
      Sum.elim (fun j => (((hβ : T') : E) ^ (j : ℕ)) w₁) (fun j => (((hβ : T') : E) ^ (j : ℕ)) w₂)
    have huu : ∀ k, ((uuQ k : VQ) : V) = uu k := by
      rintro (j | j)
      · exact hHβpow j w₁
      · exact hHβpow j w₂
    have hnotQ : ¬ LinearIndependent ℚ uuQ := by
      intro hind
      have e1 : LinearIndependent ℚ (fun k => ((uuQ k : VQ) : V)) :=
        hind.map' VQ.subtype (Submodule.ker_subtype VQ)
      let ee : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
      have e2 : LinearIndependent ℚ (fun k : Fin (n + n) => ((uuQ (ee.symm k) : VQ) : V)) :=
        e1.comp _ ee.symm.injective
      have e3 := hli (n + n) _ (fun k => (uuQ (ee.symm k)).2) e2
      have e4 : LinearIndependent L (fun k : Fin n ⊕ Fin n => ((uuQ k : VQ) : V)) := by
        have := e3.comp _ ee.injective
        convert this using 1
        funext k; simp
      apply hnotL
      convert e4 using 1
      funext k; exact (huu k).symm
    obtain ⟨aQ, haQ, k₀, hk₀⟩ := Fintype.not_linearIndependent_iff.1 hnotQ

    let r₁ : ℚ[X] := ∑ j : Fin n, Polynomial.C (aQ (Sum.inl j)) * Polynomial.X ^ (j : ℕ)
    let r₂ : ℚ[X] := ∑ j : Fin n, Polynomial.C (aQ (Sum.inr j)) * Polynomial.X ^ (j : ℕ)
    have hsum : Polynomial.aeval ((hβ : T') : E) r₁ w₁ + Polynomial.aeval ((hβ : T') : E) r₂ w₂ = 0 := by
      rw [haeval, haeval, ← haQ, Fintype.sum_sum_type]
      rfl
    have hdeg₁ : r₁.degree < n := Polynomial.degree_sum_fin_lt _
    have hdeg₂ : r₂.degree < n := Polynomial.degree_sum_fin_lt _
    by_cases hr₁ : r₁ = 0
    · exfalso
      have e1 : Polynomial.aeval ((hβ : T') : E) r₂ w₂ = 0 := by
        rwa [hr₁, map_zero, LinearMap.zero_apply, zero_add] at hsum
      have e2 : r₂ = 0 := hpolycrit w₂ hw₂ hw₂0 r₂ hdeg₂ e1
      apply hk₀
      rcases k₀ with j | j
      · rw [← coeff_sum_fin (fun j => aQ (Sum.inl j)) j, show (∑ i : Fin n, Polynomial.C (aQ (Sum.inl i))
            * Polynomial.X ^ (i : ℕ)) = r₁ from rfl, hr₁, Polynomial.coeff_zero]
      · rw [← coeff_sum_fin (fun j => aQ (Sum.inr j)) j, show (∑ i : Fin n, Polynomial.C (aQ (Sum.inr i))
            * Polynomial.X ^ (i : ℕ)) = r₂ from rfl, e2, Polynomial.coeff_zero]
    · obtain ⟨y, hy⟩ := hinv _ (hnotI r₁ hr₁ hdeg₁)
      refine ⟨-(y * Polynomial.aeval hβ r₂), ?_⟩
      have e3 := hy w₁ hw₁
      have e4 : ((Polynomial.aeval hβ r₁ : T') : E) w₁ = -(Polynomial.aeval ((hβ : T') : E) r₂ w₂) := by
        rw [hcoeaeval]
        exact eq_neg_of_add_eq_zero_left hsum
      rw [e4, map_neg] at e3
      rw [Subalgebra.coe_neg, LinearMap.neg_apply, Subalgebra.coe_mul, Module.End.mul_apply, hcoeaeval]
      exact e3.symm

  obtain ⟨wst, hwst⟩ : ∃ w : VQ, ((e : T') : E) w ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : e = 0 := Subtype.ext (LinearMap.ext h)
    have : χ' e = 0 := by rw [h0, map_zero]
    rw [hχe] at this
    exact one_ne_zero this
  let w₀ : VQ := ((e : T') : E) wst
  have hw₀K : Killed w₀ := hKe wst
  obtain ⟨yu, hyu⟩ := hcyc w₀ hw₀K hwst (ρQ t w₀) (hKρ t w₀ hw₀K)
  obtain ⟨u₀, hu₀⟩ := hsurj yu
  obtain ⟨s₀, hs₀⟩ := hsurj e

  have hmain : ((eQ s₀ : T') : E) * ρQ t = ((eQ (s₀ * u₀) : T') : E) := by
    have hce : ((e : T') : E) * ρQ t = ρQ t * ((e : T') : E) := by
      rw [← hs₀]; exact (commute_evQ_rhoQ VQ ρ hrat G s₀ t).eq
    rw [map_mul, Subalgebra.coe_mul, hs₀, hu₀, hce, hcommT e yu]
    refine LinearMap.ext fun w => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    obtain ⟨y, hy⟩ := hcyc w₀ hw₀K hwst _ (hKe w)
    rw [hy]
    obtain ⟨qy, hqy⟩ := hsurj y
    have hcy : ((y : T') : E) * ρQ t = ρQ t * ((y : T') : E) := by
      rw [← hqy]; exact (commute_evQ_rhoQ VQ ρ hrat G qy t).eq
    calc ρQ t (((y : T') : E) w₀) = ((y : T') : E) (ρQ t w₀) := by
          rw [← Module.End.mul_apply, ← hcy, Module.End.mul_apply]
      _ = ((y : T') : E) (((yu : T') : E) w₀) := by rw [← hyu]
      _ = ((yu : T') : E) (((y : T') : E) w₀) := by
          rw [← Module.End.mul_apply, hcommT, Module.End.mul_apply]

  obtain ⟨N₁, hN₁, sZ, hsZ⟩ := exists_int_multiple s₀
  obtain ⟨N₂, hN₂, uZ, huZ⟩ := exists_int_multiple u₀
  have hren_mem : ∀ q : MvPolynomial G ℤ,
      MvPolynomial.rename ((↑) : G → σ) q ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)) := by
    intro q
    have h1 : MvPolynomial.rename ((↑) : G → σ) q
        = MvPolynomial.aeval (fun g : G => (MvPolynomial.X (g : σ) : MvPolynomial σ ℤ)) q := by
      rw [MvPolynomial.rename_eq_aeval]; rfl
    rw [h1, show (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ))
        = Set.range (fun g : G => (MvPolynomial.X (g : σ) : MvPolynomial σ ℤ)) by
      ext x; simp [Set.mem_image, Set.mem_range], Algebra.adjoin_range_eq_range_aeval]
    exact ⟨q, rfl⟩
  refine ⟨MvPolynomial.C N₂ * MvPolynomial.rename ((↑) : G → σ) sZ, ?_,
    MvPolynomial.rename ((↑) : G → σ) sZ * MvPolynomial.rename ((↑) : G → σ) uZ, ?_, ?_, ?_⟩
  · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ N₂) (hren_mem sZ)
  · exact Subalgebra.mul_mem _ (hren_mem sZ) (hren_mem uZ)
  ·
    have h1 : MvPolynomial.aeval lam (MvPolynomial.rename ((↑) : G → σ) sZ) = (N₁ : L) * χ s₀ := by
      rw [← chi_map, hsZ, map_mul, chi_C, map_intCast]
    have h2 : χ s₀ = 1 := by rw [← hχe, ← hs₀]; exact (hχ' s₀).symm
    rw [map_mul, MvPolynomial.algHom_C, h1, h2, mul_one]
    simp only [algebraMap_int_eq, eq_intCast, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
    exact ⟨hN₂, hN₁⟩
  ·
    have hQ : ρQ (MvPolynomial.C N₂ * MvPolynomial.rename ((↑) : G → σ) sZ) * ρQ t
        = ρQ (MvPolynomial.rename ((↑) : G → σ) sZ * MvPolynomial.rename ((↑) : G → σ) uZ) := by
      have e1 : ρQ (MvPolynomial.rename ((↑) : G → σ) sZ)
          = ((eQ (MvPolynomial.C (N₁ : ℚ)) : T') : E) * ((eQ s₀ : T') : E) := by
        show rhoQ VQ ρ hrat (MvPolynomial.rename ((↑) : G → σ) sZ) = _
        rw [rhoQ_rename, hsZ, map_mul, Subalgebra.coe_mul]
      have e2 : ρQ (MvPolynomial.rename ((↑) : G → σ) uZ)
          = ((eQ (MvPolynomial.C (N₂ : ℚ)) : T') : E) * ((eQ u₀ : T') : E) := by
        show rhoQ VQ ρ hrat (MvPolynomial.rename ((↑) : G → σ) uZ) = _
        rw [rhoQ_rename, huZ, map_mul, Subalgebra.coe_mul]
      have e3 : ρQ (MvPolynomial.C N₂) = ((eQ (MvPolynomial.C (N₂ : ℚ)) : T') : E) := by
        show rhoQ VQ ρ hrat (MvPolynomial.C N₂) = _
        rw [eq_intCast MvPolynomial.C N₂, map_intCast, evQ_C, map_intCast]
      rw [map_mul, map_mul, e1, e2, e3]
      calc ((eQ (MvPolynomial.C (N₂ : ℚ)) : T') : E) * (((eQ (MvPolynomial.C (N₁ : ℚ)) : T') : E)
              * ((eQ s₀ : T') : E)) * ρQ t
            = ((eQ (MvPolynomial.C (N₂ : ℚ)) : T') : E) * ((eQ (MvPolynomial.C (N₁ : ℚ)) : T') : E)
              * (((eQ s₀ : T') : E) * ρQ t) := by simp only [mul_assoc]
        _ = ((eQ (MvPolynomial.C (N₂ : ℚ)) : T') : E) * ((eQ (MvPolynomial.C (N₁ : ℚ)) : T') : E)
              * ((eQ (s₀ * u₀) : T') : E) := by rw [hmain]
        _ = ((eQ (MvPolynomial.C (N₂ : ℚ) * MvPolynomial.C (N₁ : ℚ) * (s₀ * u₀)) : T') : E) := by
              rw [← Subalgebra.coe_mul, ← Subalgebra.coe_mul, ← map_mul, ← map_mul]
        _ = ((eQ (MvPolynomial.C (N₁ : ℚ) * s₀ * (MvPolynomial.C (N₂ : ℚ) * u₀)) : T') : E) := by
              rw [show (MvPolynomial.C (N₂ : ℚ) * MvPolynomial.C (N₁ : ℚ) * (s₀ * u₀) : MvPolynomial G ℚ)
                = MvPolynomial.C (N₁ : ℚ) * s₀ * (MvPolynomial.C (N₂ : ℚ) * u₀) by ring]
        _ = ((eQ (MvPolynomial.C (N₁ : ℚ)) : T') : E) * ((eQ s₀ : T') : E)
              * (((eQ (MvPolynomial.C (N₂ : ℚ)) : T') : E) * ((eQ u₀ : T') : E)) := by
              rw [← Subalgebra.coe_mul, ← Subalgebra.coe_mul, ← Subalgebra.coe_mul, ← map_mul, ← map_mul,
                ← map_mul]
    refine LinearMap.ext_on hspan (fun v hv => ?_)
    have := congrArg (fun f : E => ((f ⟨v, hv⟩ : VQ) : V)) hQ
    simp only [Module.End.mul_apply, coe_rhoQ] at this ⊢
    exact this

end Main

end RatGoodGen
p2m_reactivate "P2MW.S_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne.RatGoodGen"

theorem solution
    {L V σ : Type} [Field L] [CharZero L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ V] [IsScalarTower ℚ L V]
    (VQ : Submodule ℚ V)
    (hli : ∀ (n : ℕ) (v : Fin n → V), (∀ i, v i ∈ VQ) →
      LinearIndependent ℚ v → LinearIndependent L v)
    (hspan : Submodule.span L (VQ : Set V) = ⊤)
    (ρ : MvPolynomial σ ℤ →+* Module.End L V)
    (hrat : ∀ (i : σ) (v : V), v ∈ VQ → ρ (MvPolynomial.X i) v ∈ VQ)
    (G : Set σ)
    (hss : ∀ i ∈ G, ∃ P : Polynomial ℚ, P.Separable ∧
      Polynomial.aeval (ρ (MvPolynomial.X i)) (P.map (algebraMap ℚ L)) = 0)
    (lam : σ → L) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (heig : ∀ i ∈ G, ρ (MvPolynomial.X i) v₀ = lam i • v₀)
    (hmult : ∀ w : V, (∀ i ∈ G, ρ (MvPolynomial.X i) w = lam i • w) → ∃ c : L, w = c • v₀)
    (t : MvPolynomial σ ℤ) :
    ∃ s ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
      ∃ u ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
        MvPolynomial.aeval lam s ≠ 0 ∧ ρ s * ρ t = ρ u :=
  RatGoodGen.engine VQ hli hspan ρ hrat G hss lam v₀ hv₀ heig hmult t

end S_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne
end P2MW
export P2MW.S_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne (solution)
