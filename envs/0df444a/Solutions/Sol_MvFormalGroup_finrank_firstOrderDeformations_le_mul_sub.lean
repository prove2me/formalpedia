-- Prove2me | solution 1 for MvFormalGroup.finrank_firstOrderDeformations_le_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e277ad16-3227-5d06-9443-d47682c7180a

import Mathlib
import Definitions.Def_MvFormalGroup_Deformation
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvFormalGroup_exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow
import Theorems.Thm_MvFormalGroup_exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_finrank_firstOrderDeformations_le_mul_sub
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries MvFormalGroup

noncomputable section

namespace P2mWs2STc

section Target

variable {R : Type} [CommRing R] {d : ℕ}

abbrev XL (l : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) R := X (Sum.inl l)
abbrev XR (l : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) R := X (Sum.inr l)

def E (φ : Fin d → MvPowerSeries (Fin d) R) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R :=
  Sum.elim (fun j => subst (XL (R := R)) (φ j)) (fun j => subst (XR (R := R)) (φ j))

theorem hasSubst_XL : HasSubst (XL (R := R) (d := d)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
theorem hasSubst_XR : HasSubst (XR (R := R) (d := d)) := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_E {φ : Fin d → MvPowerSeries (Fin d) R} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst (E φ) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | j)
  · exact constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) (hφ j)
  · exact constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) (hφ j)

theorem target_eq {F G G' : MvFormalGroup d R}
    (Φ : F.Hom G) (θ : F.Hom G') (h : ∀ i, Φ.toPowerSeries i = θ.toPowerSeries i)
    (Ψ : G.Hom F) (hΦΨ : Φ.comp Ψ = MvFormalGroup.Hom.id G) (i : Fin d) :
    G'.toPowerSeries i = G.toPowerSeries i := by
  have hΦθ : Φ.toPowerSeries = θ.toPowerSeries := funext h
  have key : subst (E Φ.toPowerSeries) (G.toPowerSeries i) = subst (E Φ.toPowerSeries) (G'.toPowerSeries i) := by
    have h1 := Φ.subst_eq i
    have h2 := θ.subst_eq i
    rw [← hΦθ] at h2
    exact h1.symm.trans h2
  have hcomp : ∀ j, subst Ψ.toPowerSeries (Φ.toPowerSeries j) = X j := fun j =>
    congrArg (fun (η : MvFormalGroup.Hom G G) => η.toPowerSeries j) hΦΨ
  have hEΦ := hasSubst_E Φ.constantCoeff_eq_zero
  have hEΨ := hasSubst_E Ψ.constantCoeff_eq_zero
  have hid : (fun v => subst (E Ψ.toPowerSeries) (E Φ.toPowerSeries v)) =
      (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) := by
    funext v
    rcases v with j | j
    · show subst (E Ψ.toPowerSeries) (subst XL (Φ.toPowerSeries j)) = X (Sum.inl j)
      rw [subst_comp_subst_apply hasSubst_XL hEΨ]
      have : (fun l => subst (E Ψ.toPowerSeries) (XL (R := R) l)) = fun l => subst XL (Ψ.toPowerSeries l) := by
        funext l; exact subst_X hEΨ (Sum.inl l)
      rw [this, ← subst_comp_subst_apply Ψ.hasSubst_toPowerSeries hasSubst_XL, hcomp]
      exact subst_X hasSubst_XL j
    · show subst (E Ψ.toPowerSeries) (subst XR (Φ.toPowerSeries j)) = X (Sum.inr j)
      rw [subst_comp_subst_apply hasSubst_XR hEΨ]
      have : (fun l => subst (E Ψ.toPowerSeries) (XR (R := R) l)) = fun l => subst XR (Ψ.toPowerSeries l) := by
        funext l; exact subst_X hEΨ (Sum.inr l)
      rw [this, ← subst_comp_subst_apply Ψ.hasSubst_toPowerSeries hasSubst_XR, hcomp]
      exact subst_X hasSubst_XR j
  have := congrArg (subst (E Ψ.toPowerSeries)) key
  rw [subst_comp_subst_apply hEΦ hEΨ, subst_comp_subst_apply hEΦ hEΨ, hid] at this
  have hs := fun (f : MvPowerSeries (Fin d ⊕ Fin d) R) => congrFun (subst_self (σ := Fin d ⊕ Fin d) (R := R)) f
  simp only [id_eq] at hs
  rw [hs, hs] at this
  exact this.symm

end Target

section Dual

variable {k : Type} [CommRing k] {σ : Type}

def epart (S : MvPowerSeries σ (DualNumber k)) : MvPowerSeries σ k := fun n => TrivSqZeroExt.snd (coeff n S)

@[scoped simp] theorem coeff_epart (S : MvPowerSeries σ (DualNumber k)) (n : σ →₀ ℕ) :
    coeff n (epart S) = TrivSqZeroExt.snd (coeff n S) := rfl

theorem epart_add (S S' : MvPowerSeries σ (DualNumber k)) : epart (S + S') = epart S + epart S' := by
  ext n; simp [coeff_epart]

theorem epart_sub (S S' : MvPowerSeries σ (DualNumber k)) : epart (S - S') = epart S - epart S' := by
  ext n; simp [coeff_epart]

theorem epart_sum {ι : Type} (s : Finset ι) (S : ι → MvPowerSeries σ (DualNumber k)) :
    epart (∑ j ∈ s, S j) = ∑ j ∈ s, epart (S j) := by
  ext n
  simp only [coeff_epart, map_sum]
  exact map_sum (TrivSqZeroExt.sndHom k k) _ _

theorem epart_map_inl (P : MvPowerSeries σ k) : epart (map (TrivSqZeroExt.inlHom k k) P) = 0 := by
  ext n; simp [coeff_epart, coeff_map]

theorem epart_smul (c : k) (S : MvPowerSeries σ (DualNumber k)) : epart (c • S) = c • epart S := by
  ext n; simp [coeff_epart]

theorem epart_eps_smul (S : MvPowerSeries σ (DualNumber k)) :
    epart ((DualNumber.eps : DualNumber k) • S) = map (TrivSqZeroExt.fstHom k k k).toRingHom S := by
  ext n
  simp [coeff_epart, coeff_map, TrivSqZeroExt.snd_mul]

theorem map_fst_eps_smul (S : MvPowerSeries σ (DualNumber k)) :
    map (TrivSqZeroExt.fstHom k k k).toRingHom ((DualNumber.eps : DualNumber k) • S) = 0 := by
  ext n
  simp [coeff_map, TrivSqZeroExt.fst_mul]

theorem map_fst_map_inl (P : MvPowerSeries σ k) :
    map (TrivSqZeroExt.fstHom k k k).toRingHom (map (TrivSqZeroExt.inlHom k k) P) = P := by
  ext n; simp [coeff_map]

theorem map_fst_smul (c : k) (S : MvPowerSeries σ (DualNumber k)) :
    map (TrivSqZeroExt.fstHom k k k).toRingHom (c • S) = c • map (TrivSqZeroExt.fstHom k k k).toRingHom S := by
  ext n; simp [coeff_map]

theorem eq_map_inl_add_eps_smul (S : MvPowerSeries σ (DualNumber k)) :
    S = map (TrivSqZeroExt.inlHom k k) (map (TrivSqZeroExt.fstHom k k k).toRingHom S) +
      (DualNumber.eps : DualNumber k) • map (TrivSqZeroExt.inlHom k k) (epart S) := by
  ext n
  all_goals simp [coeff_map, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, MvPowerSeries.coeff_smul]

theorem constantCoeff_epart (S : MvPowerSeries σ (DualNumber k)) (h : constantCoeff S = 0) : constantCoeff (epart S) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply] at h ⊢
  rw [coeff_epart, h, TrivSqZeroExt.snd_zero]

theorem map_pderiv {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : σ) (F : MvPowerSeries σ R) :
    map f (pderivLin i F) = pderivLin i (map f F) := by
  ext n
  rw [coeff_map, kw_coeff_pderiv, kw_coeff_pderiv, coeff_map, map_nsmul]

end Dual

section Laws

variable {k : Type} [CommRing k] {d : ℕ}

theorem law_ext {R : Type} [CommRing R] {F G : MvFormalGroup d R} (h : ∀ i, F.toPowerSeries i = G.toPowerSeries i) : F = G := by
  obtain ⟨tF, _, _, _, _⟩ := F
  obtain ⟨tG, _, _, _, _⟩ := G
  have : tF = tG := funext h
  subst this
  rfl

theorem map_toPowerSeries {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (F : MvFormalGroup d R) (i : Fin d) :
    (F.map f).toPowerSeries i = map f (F.toPowerSeries i) := rfl

def D0 (G₀ : MvFormalGroup d k) : MvFormalGroup d (DualNumber k) := G₀.map (TrivSqZeroExt.inlHom k k)

theorem D0_map_fst (G₀ : MvFormalGroup d k) : (D0 G₀).map (TrivSqZeroExt.fstHom k k k).toRingHom = G₀ :=
  law_ext fun i => by rw [map_toPowerSeries, D0, map_toPowerSeries, map_fst_map_inl]

theorem D0_isComm (G₀ : MvFormalGroup d k) [G₀.IsComm] : (D0 G₀).IsComm where
  comm := by
    intro i
    have hsw : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) fun j => X (Sum.inl j)) :=
      hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)
    have hfam : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) (DualNumber k))) fun j => X (Sum.inl j)) =
        fun s => map (TrivSqZeroExt.inlHom k k) (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) (fun j => X (Sum.inl j)) s) := by
      funext s; rcases s with j | j <;> simp
    rw [D0, map_toPowerSeries, hfam, ← map_subst hsw, IsComm.comm]

theorem map_fst_W (Fl : MvFormalGroup d (DualNumber k)) (ηt : Fin d → MvPowerSeries (Fin d) (DualNumber k)) (l : Fin d) :
    map (TrivSqZeroExt.fstHom k k k).toRingHom
      (∑ i, subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) (DualNumber k))) (ηt i) * pderivLin (Sum.inl i) (Fl.toPowerSeries l)
        + ∑ i, subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) (DualNumber k))) (ηt i) * pderivLin (Sum.inr i) (Fl.toPowerSeries l)
        - subst Fl.toPowerSeries (ηt l)) =
      ∑ i, subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (map (TrivSqZeroExt.fstHom k k k).toRingHom (ηt i)) *
            pderivLin (Sum.inl i) ((Fl.map (TrivSqZeroExt.fstHom k k k).toRingHom).toPowerSeries l)
        + ∑ i, subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (map (TrivSqZeroExt.fstHom k k k).toRingHom (ηt i)) *
            pderivLin (Sum.inr i) ((Fl.map (TrivSqZeroExt.fstHom k k k).toRingHom).toPowerSeries l)
        - subst (Fl.map (TrivSqZeroExt.fstHom k k k).toRingHom).toPowerSeries (map (TrivSqZeroExt.fstHom k k k).toRingHom (ηt l)) := by
  simp only [map_sub, map_add, map_sum, map_mul, map_pderiv, map_toPowerSeries,
    map_subst (hasSubst_XL (R := DualNumber k) (d := d)), map_subst (hasSubst_XR (R := DualNumber k) (d := d)),
    map_subst Fl.hasSubst_toPowerSeries, XL, XR, map_X]
  rfl

end Laws

end P2mWs2STc
p2m_reactivate "P2MW.S_MvFormalGroup_finrank_firstOrderDeformations_le_mul_sub.P2mWs2STc"

end
p2m_reactivate "P2MW.S_MvFormalGroup_finrank_firstOrderDeformations_le_mul_sub.P2mWs2STc"

open P2mWs2STc in
theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    {d : ℕ} (G₀ : MvFormalGroup d k) [G₀.IsComm] (h : ℕ)
    (hheight : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (G₀.nthSeries p))) = p ^ h) :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    let δ : MvFormalGroup.Deformation G₀ (DualNumber k) → (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
      fun D i n => TrivSqZeroExt.snd (MvPowerSeries.coeff n (D.F.toPowerSeries i))
    let Z : Submodule k (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
      Submodule.span k (δ '' {D | D.F.IsComm})
    let Bdry : Submodule k (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
      Submodule.span k (δ '' {D | D.F.IsComm ∧ ∃ D' : MvFormalGroup.Deformation G₀ (DualNumber k), D.IsIso D' ∧ δ D' = 0})
    Module.Finite k (↥Z ⧸ Bdry.comap Z.subtype) ∧ Module.finrank k (↥Z ⧸ Bdry.comap Z.subtype) ≤ d * (h - d) := by
  intro δ Z Bdry
  classical
  letI instAlg : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra

  have hfst : (algebraMap (DualNumber k) k) = (TrivSqZeroExt.fstHom k k k).toRingHom := rfl

  obtain ⟨dd, Dg, hdd, hDg, hspan⟩ :=
    MvFormalGroup.exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow p G₀ h hheight
  let DG : Fin dd → MvFormalGroup.Deformation G₀ (DualNumber k) := fun j => ⟨Dg j, (hDg j).2⟩
  have hDGcomm : ∀ j, (DG j).F.IsComm := fun j => (hDg j).1
  have hgenZ : ∀ j, δ (DG j) ∈ Z := fun j => Submodule.subset_span ⟨DG j, hDGcomm j, rfl⟩

  let v : Fin dd → (↥Z ⧸ Bdry.comap Z.subtype) := fun j => Submodule.Quotient.mk ⟨δ (DG j), hgenZ j⟩
  suffices hsp : Submodule.span k (Set.range v) = ⊤ by
    constructor
    · rw [Module.finite_def, ← hsp]
      exact Submodule.fg_span (Set.finite_range v)
    · rw [← finrank_top, ← hsp]
      exact (finrank_range_le_card v).trans (by rw [Fintype.card_fin]; exact hdd)

  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction hz using Submodule.span_induction with
  | zero =>
    have : (⟨0, Submodule.zero_mem _⟩ : ↥Z) = 0 := rfl
    rw [this, Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
  | add z z' hz hz' ih ih' =>
    have : (⟨z + z', Submodule.add_mem _ hz hz'⟩ : ↥Z) = ⟨z, hz⟩ + ⟨z', hz'⟩ := rfl
    rw [this, Submodule.Quotient.mk_add]; exact Submodule.add_mem _ ih ih'
  | smul c z hz ih =>
    have : (⟨c • z, Submodule.smul_mem _ c hz⟩ : ↥Z) = c • ⟨z, hz⟩ := rfl
    rw [this, Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ c ih
  | mem z hzmem =>
    obtain ⟨D, hDcomm, rfl⟩ := hzmem
    haveI : D.F.IsComm := hDcomm

    obtain ⟨c, G, θ, hG, hθ⟩ := hspan D.F D.map_eq

    set η : Fin d → MvPowerSeries (Fin d) k := fun i => epart (θ.toPowerSeries i) with hη
    have hηcc : ∀ (_ : Unit) (i : Fin d), constantCoeff (-(MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (η i))) = 0 := by
      intro _ i
      rw [map_neg, neg_eq_zero, constantCoeff_map, constantCoeff_epart _ (θ.constantCoeff_eq_zero i), map_zero]
    have hεε : ∀ (_ _ : Unit), (DualNumber.eps : DualNumber k) * DualNumber.eps = 0 := fun _ _ => DualNumber.eps_mul_eps
    have hθdec : ∀ i, θ.toPowerSeries i = X i - ∑ u : Unit, (fun _ : Unit => (DualNumber.eps : DualNumber k)) u •
        (fun (_ : Unit) (i : Fin d) => -(MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (η i))) u i := by
      intro i
      rw [Fintype.sum_unique, smul_neg, sub_neg_eq_add]
      conv_lhs => rw [eq_map_inl_add_eps_smul (θ.toPowerSeries i), hθ i, MvPowerSeries.map_X]

    obtain ⟨G', Φ', Ψ', hΦ', -, -, h2', -, hG'⟩ :=
      MvFormalGroup.exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero (fun _ : Unit => (DualNumber.eps : DualNumber k)) hεε
        (fun (_ : Unit) (i : Fin d) => -(MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (η i))) hηcc G
    obtain ⟨F'', Φ'', Ψ'', hΦ'', hΨ'', h1'', h2'', hcomm'', hF''⟩ :=
      MvFormalGroup.exists_hom_toPowerSeries_eq_add_sum_smul_of_mul_eq_zero (fun _ : Unit => (DualNumber.eps : DualNumber k)) hεε
        (fun (_ : Unit) (i : Fin d) => -(MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (η i))) hηcc (D0 G₀)

    have hDG' : ∀ i, D.F.toPowerSeries i = G'.toPowerSeries i :=
      fun i => target_eq Φ' θ (fun i => by rw [hΦ', hθdec]) Ψ' h2' i

    have hGfst : G.map (TrivSqZeroExt.fstHom k k k).toRingHom = (D0 G₀).map (TrivSqZeroExt.fstHom k k k).toRingHom := by
      rw [D0_map_fst]
      refine law_ext fun i => ?_
      have hDgi : ∀ j, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom ((Dg j).toPowerSeries i) = G₀.toPowerSeries i :=
        fun j => by rw [← map_toPowerSeries, (hDg j).2]
      rw [map_toPowerSeries, hG i, map_add, map_sum, map_fst_map_inl]
      simp only [map_fst_smul, map_sub, hDgi, map_fst_map_inl, sub_self, smul_zero, Finset.sum_const_zero, add_zero]
    have hF''map : F''.map (algebraMap (DualNumber k) k) = G₀ := by
      rw [hfst]
      refine law_ext fun i => ?_
      rw [map_toPowerSeries, hF'' i, map_add, Fintype.sum_unique, map_fst_eps_smul, add_zero, ← map_toPowerSeries, D0_map_fst]
    let DF : MvFormalGroup.Deformation G₀ (DualNumber k) := ⟨F'', hF''map⟩
    let DT : MvFormalGroup.Deformation G₀ (DualNumber k) := ⟨D0 G₀, by rw [hfst]; exact D0_map_fst G₀⟩
    have hDFcomm : DF.F.IsComm := hcomm'' (D0_isComm G₀)
    have hDFiso : DF.IsIso DT := by
      refine ⟨Ψ'', ⟨Φ'', h2'', h1''⟩, fun i => ?_⟩
      rw [hfst, hΨ'' i, map_add, Fintype.sum_unique, map_fst_eps_smul, add_zero, MvPowerSeries.map_X]
    have hδDT : δ DT = 0 := by
      funext i
      show epart ((D0 G₀).toPowerSeries i) = 0
      rw [D0, map_toPowerSeries, epart_map_inl]
    have hBdry : δ DF ∈ Bdry := Submodule.subset_span ⟨DF, ⟨hDFcomm, DT, hDFiso, hδDT⟩, rfl⟩
    have hDFZ : δ DF ∈ Z := Submodule.subset_span ⟨DF, hDFcomm, rfl⟩

    have hδ : δ D = ∑ j, c j • δ (DG j) + δ DF := by
      funext i
      show epart (D.F.toPowerSeries i) = (∑ j, c j • δ (DG j) + δ DF) i
      rw [Pi.add_apply, Finset.sum_apply]
      show epart (D.F.toPowerSeries i) = ∑ j, (c j • δ (DG j)) i + epart (F''.toPowerSeries i)
      simp only [Pi.smul_apply]
      show epart (D.F.toPowerSeries i) = ∑ j, c j • epart ((Dg j).toPowerSeries i) + epart (F''.toPowerSeries i)
      rw [hDG', hG', hF'']
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [epart_add, epart_add, epart_eps_smul, epart_eps_smul, map_fst_W, map_fst_W, hGfst,
        show epart ((D0 G₀).toPowerSeries i) = 0 by rw [D0, map_toPowerSeries, epart_map_inl], zero_add]
      congr 1
      rw [hG, epart_add, epart_map_inl, zero_add, epart_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [epart_smul, epart_sub, epart_map_inl, sub_zero]

    have hZeq : (⟨δ D, Submodule.subset_span ⟨D, hDcomm, rfl⟩⟩ : ↥Z) = ∑ j, c j • ⟨δ (DG j), hgenZ j⟩ + ⟨δ DF, hDFZ⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, hδ]
    rw [hZeq, Submodule.Quotient.mk_add, ← Submodule.mkQ_apply, map_sum]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => ?_) ?_
    · rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · have : (Bdry.comap Z.subtype).mkQ ⟨δ DF, hDFZ⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hBdry
      rw [← Submodule.mkQ_apply, this]; exact Submodule.zero_mem _

end S_MvFormalGroup_finrank_firstOrderDeformations_le_mul_sub
end P2MW
export P2MW.S_MvFormalGroup_finrank_firstOrderDeformations_le_mul_sub (solution)
