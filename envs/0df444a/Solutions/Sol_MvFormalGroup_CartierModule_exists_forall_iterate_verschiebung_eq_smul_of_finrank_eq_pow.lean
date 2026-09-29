-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/79d63eab-596f-5bf2-9034-31d1337f28ff

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Theorems.Thm_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

noncomputable section

namespace P2mKcCartierVnil

set_option linter.unusedSectionVars false

open MvPowerSeries MvFormalGroup

section Blocks

variable {k : Type u} [CommRing k] {d : ℕ}

def blkExt (c : Fin d → MvPowerSeries (Fin d) k) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))

theorem blkExt_inl (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt c (Sum.inl j) = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j) := rfl

theorem blkExt_inr (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt c (Sum.inr j) = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j) := rfl

theorem hasSubst_inl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_blkExt {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0)
    (s : Fin d ⊕ Fin d) : (blkExt c s).constantCoeff = 0 := by
  rcases s with j | j
  · exact constantCoeff_subst_eq_zero (hasSubst_inl (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  · exact constantCoeff_subst_eq_zero (hasSubst_inr (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)

theorem hasSubst_blkExt {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0) :
    HasSubst (blkExt c) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blkExt hc)

theorem subst_elim_blkExt {τ : Type*} {a b : Fin d → MvPowerSeries τ k}
    (ha : HasSubst a) (hb : HasSubst b) (c : Fin d → MvPowerSeries (Fin d) k) (s : Fin d ⊕ Fin d) :
    subst (Sum.elim a b) (blkExt c s) = Sum.elim (fun j => subst a (c j)) (fun j => subst b (c j)) s := by
  have hab : HasSubst (Sum.elim a b) := by
    refine ⟨?_, ?_⟩
    · rintro (l | l)
      · exact ha.const_coeff l
      · exact hb.const_coeff l
    · intro e
      have h1 := (ha.coeff_zero e)
      have h2 := (hb.coeff_zero e)
      refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
      rintro (l | l) hl
      · exact Or.inl ⟨l, hl, rfl⟩
      · exact Or.inr ⟨l, hl, rfl⟩
  rcases s with j | j
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) =
      subst a (c j)
    rw [subst_comp_subst_apply (hasSubst_inl (k := k) (d := d)) hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inl l)
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) =
      subst b (c j)
    rw [subst_comp_subst_apply (hasSubst_inr (k := k) (d := d)) hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inr l)

theorem subst_blkExt_blkExt {c c' : Fin d → MvPowerSeries (Fin d) k}
    (hc : ∀ i, (c i).constantCoeff = 0) (s : Fin d ⊕ Fin d) :
    subst (blkExt c) (blkExt c' s) = blkExt (fun j => subst c (c' j)) s := by
  have hcs := hasSubst_of_constantCoeff_zero hc
  have h := subst_elim_blkExt (k := k) (d := d)
    (a := fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (b := fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (hasSubst_of_constantCoeff_zero fun j =>
      constantCoeff_subst_eq_zero (hasSubst_inl (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j))
    (hasSubst_of_constantCoeff_zero fun j =>
      constantCoeff_subst_eq_zero (hasSubst_inr (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j))
    c' s
  refine h.trans ?_
  rcases s with j | j
  · show subst (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) (c' j) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_inl (k := k) (d := d))]
  · show subst (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) (c' j) =
      subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_inr (k := k) (d := d))]

theorem blkExt_X : blkExt (fun i : Fin d => (X i : MvPowerSeries (Fin d) k)) =
    fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) k) := by
  funext s
  rcases s with j | j
  · exact subst_X (hasSubst_inl (k := k) (d := d)) j
  · exact subst_X (hasSubst_inr (k := k) (d := d)) j

theorem blkExt_X_pow (n : ℕ) : blkExt (fun i : Fin d => (X i : MvPowerSeries (Fin d) k) ^ n) =
    fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) k) ^ n := by
  funext s
  rcases s with j | j
  · show subst _ (X j ^ n) = _
    rw [subst_pow (hasSubst_inl (k := k) (d := d)), subst_X (hasSubst_inl (k := k) (d := d))]
  · show subst _ (X j ^ n) = _
    rw [subst_pow (hasSubst_inr (k := k) (d := d)), subst_X (hasSubst_inr (k := k) (d := d))]

theorem subst_blkExt_injective {α β : Fin d → MvPowerSeries (Fin d) k}
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) :
    Function.Injective (fun g : MvPowerSeries (Fin d ⊕ Fin d) k => subst (blkExt β) g) := by
  intro g g' hgg'
  have h := congrArg (subst (blkExt α)) hgg'
  simp only at h
  rwa [subst_comp_subst_apply (hasSubst_blkExt hβ0) (hasSubst_blkExt hα0),
    subst_comp_subst_apply (hasSubst_blkExt hβ0) (hasSubst_blkExt hα0),
    funext (subst_blkExt_blkExt hα0), funext hαβ, blkExt_X, subst_self] at h

end Blocks

section Inverse

variable {k : Type u} [Field k] {d : ℕ}

def lin (C : Matrix (Fin d) (Fin d) k) : Fin d → MvPowerSeries (Fin d) k :=
  fun i => ∑ j, C i j • (X j : MvPowerSeries (Fin d) k)

theorem constantCoeff_lin (C : Matrix (Fin d) (Fin d) k) (i : Fin d) : (lin C i).constantCoeff = 0 := by
  unfold lin
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

theorem hasSubst_lin (C : Matrix (Fin d) (Fin d) k) : HasSubst (lin C) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_lin C)

theorem subst_smul_sum {τ : Type*} {F : Fin d → MvPowerSeries τ k} (hF : HasSubst F)
    (C : Matrix (Fin d) (Fin d) k) (G : Fin d → MvPowerSeries (Fin d) k) (i : Fin d) :
    subst F (∑ j, C i j • G j) = ∑ j, C i j • subst F (G j) := by
  rw [← coe_substAlgHom hF, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

theorem subst_lin {τ : Type*} {F : Fin d → MvPowerSeries τ k} (hF : HasSubst F)
    (C : Matrix (Fin d) (Fin d) k) (i : Fin d) : subst F (lin C i) = ∑ j, C i j • F j := by
  unfold lin
  rw [subst_smul_sum hF]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [subst_X hF]

theorem smul_sum_lin (C D : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    (∑ j, D i j • lin C j) = lin (D * C) i := by
  unfold lin
  simp_rw [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem subst_lin_lin (C D : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    subst (lin C) (lin D i) = lin (D * C) i := by
  rw [subst_lin (hasSubst_lin C), smul_sum_lin]

theorem lin_one : lin (1 : Matrix (Fin d) (Fin d) k) = fun i => (X i : MvPowerSeries (Fin d) k) := by
  funext i
  unfold lin
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem linearPart_smul_sum (C : Matrix (Fin d) (Fin d) k) (G : Fin d → MvPowerSeries (Fin d) k) :
    linearPart (fun i => ∑ j, C i j • G j) = C * linearPart G := by
  ext i l
  simp only [linearPart, Matrix.of_apply, Matrix.mul_apply, map_sum, map_smul, smul_eq_mul]

theorem exists_inverse (ψ : Fin d → MvPowerSeries (Fin d) k) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hA : IsUnit (linearPart ψ)) :
    ∃ v : Fin d → MvPowerSeries (Fin d) k, (∀ i, (v i).constantCoeff = 0) ∧
      (∀ i, subst ψ (v i) = X i) ∧ (∀ i, subst v (ψ i) = X i) := by
  obtain ⟨⟨A, B, hAB, hBA⟩, hAeq⟩ := hA
  have hAeq' : A = linearPart ψ := hAeq

  let ψt : Fin d → MvPowerSeries (Fin d) k := fun i => ∑ j, B i j • ψ j
  have hψt0 : ∀ i, (ψt i).constantCoeff = 0 := by
    intro i
    show constantCoeff (∑ j, B i j • ψ j) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_eq_C_mul, map_mul, hψ0, mul_zero]
  have hlin : linearPart ψt = 1 := by
    show linearPart (fun i => ∑ j, B i j • ψ j) = 1
    rw [linearPart_smul_sum, ← hAeq', hBA]
  obtain ⟨u, hu0, hu1, hu2⟩ :=
    MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one ψt hψt0 hlin
  have hus := hasSubst_of_constantCoeff_zero hu0
  have hψs := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun i => subst (lin B) (u i), fun i => constantCoeff_subst_eq_zero (hasSubst_lin B)
    (constantCoeff_lin B) (hu0 i), fun i => ?_, fun i => ?_⟩
  · rw [subst_comp_subst_apply (hasSubst_lin B) hψs]
    have : (fun j => subst ψ (lin B j)) = ψt := funext fun j => subst_lin hψs B j
    rw [this, hu1]
  ·
    have hS : ∀ j, (∑ l, B j l • subst u (ψ l)) = X j := by
      intro j
      rw [← subst_smul_sum hus, hu2 j]
    have hS' : ∀ i, subst u (ψ i) = lin A i := by
      intro i
      have h1 : (∑ j, A i j • ∑ l, B j l • subst u (ψ l)) = ∑ j, A i j • (X j : MvPowerSeries (Fin d) k) :=
        Finset.sum_congr rfl fun j _ => by rw [hS j]
      have h2 : (∑ j, A i j • ∑ l, B j l • subst u (ψ l)) = subst u (ψ i) := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, hAB]
        rw [Finset.sum_eq_single i]
        · rw [Matrix.one_apply_eq, one_smul]
        · intro l _ hl
          rw [Matrix.one_apply_ne (Ne.symm hl), zero_smul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [← h2, h1]
      rfl
    have hvs : HasSubst (fun j => subst (lin B) (u j)) := hasSubst_of_constantCoeff_zero fun j =>
      constantCoeff_subst_eq_zero (hasSubst_lin B) (constantCoeff_lin B) (hu0 j)
    rw [← subst_comp_subst_apply hus (hasSubst_lin B), hS', subst_lin_lin, hAB, lin_one]

variable {Ψ Φ : MvFormalGroup d k}

def invHom (ψ : Ψ.Hom Φ) (v : Fin d → MvPowerSeries (Fin d) k) (hv0 : ∀ i, (v i).constantCoeff = 0)
    (hψv : ∀ i, subst ψ.toPowerSeries (v i) = X i) (hvψ : ∀ i, subst v (ψ.toPowerSeries i) = X i) :
    Φ.Hom Ψ where
  toPowerSeries := v
  constantCoeff_eq_zero := hv0
  subst_eq := by
    intro i
    apply subst_blkExt_injective hv0 ψ.constantCoeff_eq_zero hvψ
    show subst (blkExt ψ.toPowerSeries) (subst Φ.toPowerSeries (v i)) =
      subst (blkExt ψ.toPowerSeries) (subst (blkExt v) (Ψ.toPowerSeries i))
    have hβ := hasSubst_blkExt ψ.constantCoeff_eq_zero
    rw [subst_comp_subst_apply Φ.hasSubst_toPowerSeries hβ,
      subst_comp_subst_apply (hasSubst_blkExt hv0) hβ,
      funext (subst_blkExt_blkExt ψ.constantCoeff_eq_zero), funext hψv, blkExt_X, subst_self]
    have hfam : (fun j => subst (blkExt ψ.toPowerSeries) (Φ.toPowerSeries j)) =
        fun j => subst Ψ.toPowerSeries (ψ.toPowerSeries j) := funext fun j => (ψ.subst_eq j).symm
    rw [hfam, ← subst_comp_subst_apply ψ.hasSubst_toPowerSeries Ψ.hasSubst_toPowerSeries, hψv,
      subst_X Ψ.hasSubst_toPowerSeries]
    rfl

theorem comp_invHom (ψ : Ψ.Hom Φ) (v : Fin d → MvPowerSeries (Fin d) k) (hv0 : ∀ i, (v i).constantCoeff = 0)
    (hψv : ∀ i, subst ψ.toPowerSeries (v i) = X i) (hvψ : ∀ i, subst v (ψ.toPowerSeries i) = X i) :
    ψ.comp (invHom ψ v hv0 hψv hvψ) = Hom.id Φ :=
  Hom.ext (funext fun i => hvψ i)

theorem isUnit_of_rank_eq (A : Matrix (Fin d) (Fin d) k) (h : A.rank = d) : IsUnit A := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hr : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h
  intro y
  have hy : y ∈ LinearMap.range A.mulVecLin := hr ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

end Inverse

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}

local notation "σ" => frobenius k p

open MvFormalGroup.CartierModule

variable (Ψ : MvFormalGroup d k) [Ψ.IsComm]

def frob1 : Ψ.Hom (Ψ.map σ) where
  toPowerSeries := fun i => (X i : MvPowerSeries (Fin d) k) ^ p
  constantCoeff_eq_zero := by
    intro i
    rw [map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]
  subst_eq := by
    intro i
    haveI : ExpChar k p := ExpChar.prime hp.out
    rw [subst_pow Ψ.hasSubst_toPowerSeries, subst_X Ψ.hasSubst_toPowerSeries,
      ← map_frobenius_expand p hp.out.ne_zero, map_expand, MvPowerSeries.expand, substAlgHom_apply]
    show _ = subst _ (MvPowerSeries.map σ (Ψ.toPowerSeries i))
    congr 1
    funext s
    rcases s with j | j
    · show (X (Sum.inl j)) ^ p = subst _ ((X j : MvPowerSeries (Fin d) k) ^ p)
      rw [subst_pow (hasSubst_inl (k := k) (d := d)), subst_X (hasSubst_inl (k := k) (d := d))]
    · show (X (Sum.inr j)) ^ p = subst _ ((X j : MvPowerSeries (Fin d) k) ^ p)
      rw [subst_pow (hasSubst_inr (k := k) (d := d)), subst_X (hasSubst_inr (k := k) (d := d))]

theorem frob1_toPowerSeries (i : Fin d) : (frob1 Ψ).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p :=
  rfl

theorem map_frob1 (y : CartierModule p Ψ) :
    map (frob1 Ψ) y = verschiebung (baseChange σ y) := by
  haveI : ExpChar k p := ExpChar.prime hp.out
  refine CartierModule.ext (funext fun j => ?_)
  rw [toPowerSeries_verschiebung_eq_expand]
  show subst y.toPowerSeries ((X j : MvPowerSeries (Fin d) k) ^ p) =
    MvPowerSeries.expand p _ (MvPowerSeries.map σ (y.toPowerSeries j))
  rw [subst_pow y.hasSubst_toPowerSeries, subst_X y.hasSubst_toPowerSeries,
    ← map_expand p hp.out.ne_zero, map_frobenius_expand]

theorem baseChange_frobenius_surjective :
    Function.Surjective (baseChange (p := p) (Φ := Ψ) σ) := by
  intro z
  set σi : k →+* k := (frobeniusEquiv k p).symm.toRingHom with hσi
  have hcomp : σi.comp σ = RingHom.id k := by
    refine RingHom.ext fun a => ?_
    show (frobeniusEquiv k p).symm (frobenius k p a) = a
    rw [← coe_frobeniusEquiv, RingEquiv.symm_apply_apply]
  have h : (Ψ.map σ).map σi = Ψ := by
    rw [map_map_ringHom, hcomp, map_ringHom_id']
  refine ⟨baseChangeEq σi h z, ?_⟩
  refine CartierModule.ext (funext fun j => ?_)
  show MvPowerSeries.map σ (MvPowerSeries.map σi (z.toPowerSeries j)) = z.toPowerSeries j
  ext e
  rw [coeff_map, coeff_map]
  show frobenius k p ((frobeniusEquiv k p).symm _) = _
  rw [← coe_frobeniusEquiv, RingEquiv.apply_symm_apply]

theorem exists_verschiebung_eq_map {Ψ' : MvFormalGroup d k} [Ψ'.IsComm] (π : Ψ.Hom Ψ')
    (ρ : Ψ'.Hom (Ψ.map σ)) (hρπ : ∀ i, (ρ.comp π).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p)
    (hρfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ρ.toPowerSeries)))
    (y' : CartierModule p Ψ') : ∃ y : CartierModule p Ψ, verschiebung y' = map π y := by
  obtain ⟨y, hy⟩ := baseChange_frobenius_surjective Ψ (map ρ y')
  have hρπ' : ρ.comp π = frob1 Ψ := Hom.ext (funext hρπ)
  refine ⟨y, ?_⟩
  apply MvFormalGroup.CartierModule.map_injective_of_finite_quotient p Ψ' (Ψ.map σ) ρ hρfin
  rw [map_verschiebung, ← hy, ← map_frob1, ← hρπ', CartierModule.map_comp]

end Frobenius

section Main

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}

open MvFormalGroup.CartierModule

private theorem _root_.P2mKcCartierVnil.finrank_pos {Ψ Φ : MvFormalGroup d k} (ψ : Ψ.Hom Φ)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    0 < Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) := by
  have hne : Ideal.span (Set.range ψ.toPowerSeries) ≠ ⊤ := by
    intro htop
    have hle : Ideal.span (Set.range ψ.toPowerSeries) ≤
        RingHom.ker (constantCoeff : MvPowerSeries (Fin d) k →+* k) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact ψ.constantCoeff_eq_zero i
    rw [htop, top_le_iff] at hle
    have h1 : (1 : MvPowerSeries (Fin d) k) ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin d) k →+* k) :=
      hle ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI := Ideal.Quotient.nontrivial_iff.mpr hne
  exact Module.finrank_pos

p2m_export "P2mKcCartierVnil" "finrank_pos"
variable (Φ : MvFormalGroup d k) [Φ.IsComm]

theorem key : ∀ (n : ℕ) (Ψ : MvFormalGroup d k) (_ : Ψ.IsComm) (ψ : Ψ.Hom Φ),
    Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) →
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) ≤ n →
    ∃ N : ℕ, ∀ x : CartierModule p Φ, ∃ y : CartierModule p Ψ,
      (⇑(verschiebung (p := p) (Φ := Φ)))^[N] x = map ψ y := by
  intro n
  induction n with
  | zero =>
    intro Ψ _ ψ hfin hle
    exact absurd hle (not_le.mpr (finrank_pos ψ hfin))
  | succ n ih =>
    intro Ψ hΨ ψ hfin hle
    haveI := hΨ
    obtain ⟨Ψ', hΨ', π, ρ, ψ', hψ'π, hρπ, hrank, -, hρfin, hψ'fin, hdegmul⟩ :=
      MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul p Ψ Φ ψ hfin
    haveI := hΨ'
    set r := (MvFormalGroup.linearPart ψ.toPowerSeries).rank with hr
    by_cases hdr : d - r = 0
    ·
      have hrd : r = d := le_antisymm (hr ▸ Matrix.rank_le_width _) (Nat.sub_eq_zero_iff_le.mp hdr)
      have hunit : IsUnit (MvFormalGroup.linearPart ψ.toPowerSeries) :=
        isUnit_of_rank_eq _ (hr ▸ hrd)
      obtain ⟨v, hv0, hψv, hvψ⟩ := exists_inverse ψ.toPowerSeries ψ.constantCoeff_eq_zero hunit
      refine ⟨0, fun x => ⟨map (invHom ψ v hv0 hψv hvψ) x, ?_⟩⟩
      rw [← CartierModule.map_comp, comp_invHom, CartierModule.map_id]
      rfl
    ·
      have hpow : 2 ≤ p ^ (d - r) :=
        le_trans hp.out.two_le (Nat.le_self_pow hdr p)
      have hpos' := finrank_pos ψ' hψ'fin
      have hlt : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ≤ n := by
        have h1 : 2 * Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ≤
            Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) := by
          rw [hdegmul]
          exact Nat.mul_le_mul_right _ hpow
        omega
      obtain ⟨N', hN'⟩ := ih Ψ' hΨ' ψ' hψ'fin hlt
      refine ⟨N' + 1, fun x => ?_⟩
      obtain ⟨y', hy'⟩ := hN' x
      obtain ⟨y, hy⟩ := exists_verschiebung_eq_map Ψ π ρ hρπ hρfin y'
      refine ⟨y, ?_⟩
      have hψeq : ψ = ψ'.comp π := (Hom.ext (funext hψ'π)).symm
      rw [Function.iterate_succ_apply', hy', ← map_verschiebung, hy, ← CartierModule.map_comp, ← hψeq]

theorem main (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    ∃ N : ℕ, ∀ f : CartierModule p Φ, ∃ g : CartierModule p Φ,
      (⇑(verschiebung (p := p) (Φ := Φ)))^[N] f = (p : WittVector p k) • g := by
  let ψ : Φ.Hom Φ := ((p : ℕ) : MvFormalGroup.End Φ)
  have hψ : ψ.toPowerSeries = Φ.nthSeries p := MvFormalGroup.End.toPowerSeries_natCast _ p
  have hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) := by
    rw [hψ]
    exact Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos hp.out.pos h)
  obtain ⟨N, hN⟩ := key Φ (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)))
    Φ inferInstance ψ hfin le_rfl
  refine ⟨N, fun f => ?_⟩
  obtain ⟨g, hg⟩ := hN f
  refine ⟨g, ?_⟩
  rw [hg]
  show map ((p : ℕ) : MvFormalGroup.End Φ) g = _
  rw [← endAct_apply, endAct_natCast, natCast_smul_eq_nsmul']

end Main

end P2mKcCartierVnil

end

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm] (h : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h) :
    ∃ N : ℕ, ∀ f : MvFormalGroup.CartierModule p Φ, ∃ g : MvFormalGroup.CartierModule p Φ,
      (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] f =
        (p : WittVector p k) • g :=
  P2mKcCartierVnil.main Φ h hdeg

end S_MvFormalGroup_CartierModule_exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow (solution)
