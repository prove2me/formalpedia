-- Prove2me | solution 1 for LinearEquiv.exists_forall_finrank_inf_map_pow_add_finrank_inf_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/40ed408c-ca1d-5a2c-ae30-c3c2906397c5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open Submodule LinearMap Module

namespace Ef8d
variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem map_pow_le {ψ : W →ₗ[k] W} {S : Submodule k W} (hS : S.map ψ ≤ S) :
    ∀ M : ℕ, S.map (ψ^M) ≤ S := by
  intro M; induction M with
  | zero => rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  | succ n ih =>
    rw [pow_succ, show (ψ^n * ψ : W→ₗ[k]W) = (ψ^n).comp ψ from rfl, Submodule.map_comp]
    exact (Submodule.map_mono hS).trans ih

theorem mem_of_pow_map {ψ : W →ₗ[k] W} {S : Submodule k W} (hS : S.map ψ ≤ S)
    (M : ℕ) {x : W} (hx : x ∈ S) : (ψ^M) x ∈ S :=
  map_pow_le hS M ⟨x, hx, rfl⟩

def barEnd (φ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map φ ≤ P) (hB : B.map φ ≤ B) :
    (B ⧸ P.comap B.subtype) →ₗ[k] (B ⧸ P.comap B.subtype) :=
  (P.comap B.subtype).mapQ (P.comap B.subtype) (φ.restrict (fun x hx => hB ⟨x, hx, rfl⟩))
    (fun x hx => by simp only [mem_comap, coe_subtype] at hx ⊢; exact hP ⟨(x : W), hx, rfl⟩)

theorem finiteDimensional_quot_of_monicTorsion
    (φ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map φ ≤ P) (hB : B.map φ ≤ B)
    (S : Submodule k W) (hSB : S ≤ B) [FiniteDimensional k S]
    (hgen : B ≤ ⨆ j : ℕ, S.map (φ ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧ Polynomial.aeval φ c y ∈ P) :
    FiniteDimensional k (B ⧸ P.comap B.subtype) := by
  classical
  have key : ∀ (s : W) (c : Polynomial k), c.Monic → Polynomial.aeval φ c s ∈ P →
      ∀ m, (φ^m) s ∈
        P ⊔ Submodule.span k ((Finset.range c.natDegree).image (fun j => (φ^j) s)) := by
    intro s c hc hcs
    set d := c.natDegree with hd
    have happ : (φ^d) s + ∑ j ∈ Finset.range d, c.coeff j • (φ^j) s
        = (Polynomial.aeval φ c) s := by
      conv_rhs => rw [hc.as_sum]
      simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
        LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      simp only [← hd]
    have hd_expr : (φ^d) s =
        (Polynomial.aeval φ c) s - ∑ j ∈ Finset.range d, c.coeff j • (φ^j) s :=
      eq_sub_of_add_eq happ
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases lt_or_ge m d with hm | hm
      · exact Submodule.mem_sup_right
          (Submodule.subset_span (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩))
      · have hsplit : (φ^m) s = (φ^(m-d)) ((φ^d) s) := by
          have h : (φ^((m-d)+d)) s = (φ^(m-d)) ((φ^d) s) := by rw [pow_add]; rfl
          rwa [Nat.sub_add_cancel hm] at h
        rw [hsplit, hd_expr, map_sub, map_sum]
        refine sub_mem ?_ (Submodule.sum_mem _ fun j hj => ?_)
        · exact Submodule.mem_sup_left (mem_of_pow_map hP (m-d) hcs)
        · rw [map_smul]
          refine Submodule.smul_mem _ _ ?_
          have hlt : (m - d) + j < m := by
            have := Finset.mem_range.mp hj; omega
          have heq : (φ^(m-d)) ((φ^j) s) = (φ^((m-d)+j)) s := by rw [pow_add]; rfl
          rw [heq]; exact ih _ hlt
  have hSfg : S.FG := by
    have h1 : (⊤ : Submodule k ↥S).FG := Module.finite_def.mp inferInstance
    have h2 : S = (⊤ : Submodule k ↥S).map S.subtype := by
      rw [Submodule.map_top, Submodule.range_subtype]
    rw [h2]; exact h1.map _
  obtain ⟨σ, hσ⟩ := hSfg
  have hσB : ∀ s ∈ σ, s ∈ B := fun s hs => hSB (hσ ▸ Submodule.subset_span hs)
  choose! c hcMon hcP using fun s (hs : s ∈ σ) => htor s (hσB s hs)
  let Tof : W → Submodule k W := fun s =>
    Submodule.span k ((Finset.range (c s).natDegree).image (fun j => (φ^j) s))
  let T : Submodule k W := σ.sup Tof
  haveI hTfd : FiniteDimensional k ↥T :=
    Module.Finite.iff_fg.mpr (Submodule.fg_finset_sup σ Tof fun s _ =>
      Submodule.fg_span (Finset.image _ _).finite_toSet)
  have hTB : T ≤ B := Finset.sup_le fun s hs => Submodule.span_le.mpr fun x hx => by
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_range] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact mem_of_pow_map hB j (hσB s hs)
  have hBPT : B ≤ P ⊔ T := by
    refine hgen.trans (iSup_le fun j => ?_)
    rw [← hσ, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact (sup_le_sup_left (Finset.le_sup hs : Tof s ≤ T) P)
      (key s (c s) (hcMon s hs) (hcP s hs) j)
  haveI : FiniteDimensional k ↥(T.comap B.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hTB).symm
  refine Module.Finite.of_surjective
    ((P.comap B.subtype).mkQ ∘ₗ (T.comap B.subtype).subtype) ?_
  intro q
  obtain ⟨⟨b, hbB⟩, rfl⟩ := (P.comap B.subtype).mkQ_surjective q
  obtain ⟨p, hpP, t, htT, hbpt⟩ := Submodule.mem_sup.mp (hBPT hbB)
  have htB : t ∈ B := hTB htT
  refine ⟨⟨⟨t, htB⟩, Submodule.mem_comap.mpr htT⟩, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
  refine (Submodule.Quotient.eq _).mpr ?_
  refine Submodule.mem_comap.mpr ?_
  show (t : W) - b ∈ P
  have hneg : (t : W) - b = -p := by rw [← hbpt]; abel
  rw [hneg]; exact P.neg_mem hpP

theorem disjoint_ker_pow_range_pow_aux {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (g : V →ₗ[k] V) :
    ∃ M₀, ∀ M ≥ M₀, Disjoint (LinearMap.ker (g^M)) (LinearMap.range (g^M)) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp g.eventually_iSup_ker_pow_eq
  refine ⟨N₀, fun M hM => ?_⟩
  rw [Submodule.disjoint_def]
  rintro v hvk ⟨w, hw⟩
  have hwk : w ∈ LinearMap.ker (g^(M+M)) := by
    rw [LinearMap.mem_ker, pow_add]
    change (g^M) ((g^M) w) = 0
    rw [hw]; exact hvk
  have hsub : LinearMap.ker (g^(M+M)) ≤ LinearMap.ker (g^M) := by
    rw [← hN₀ M hM]; exact le_iSup (fun m => LinearMap.ker (g^m)) (M+M)
  have : (g^M) w = 0 := hsub hwk
  rw [← hw, this]

theorem fitting_step
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (f : V₁ →ₗ[k] V₁) (g : V₂ →ₗ[k] V₂) (S : Submodule k (V₁ × V₂)) :
    ∃ M₀, ∀ M ≥ M₀,
      Module.finrank k S ≤
        Module.finrank k ↥(S.map (LinearMap.prodMap (f ^ M) LinearMap.id) ⊔
          S.map (LinearMap.prodMap LinearMap.id (g ^ M))) := by
  obtain ⟨N₀, hN₀⟩ := disjoint_ker_pow_range_pow_aux g
  refine ⟨N₀, fun M hM => ?_⟩
  set ψ : (V₁ × V₂) →ₗ[k] (V₁ × V₂) := LinearMap.prodMap LinearMap.id (g ^ M) with hψ
  set T := S.map ψ with hT
  set J : Submodule k (V₁ × V₂) := S ⊓ LinearMap.ker ψ with hJ
  have hkerψ : LinearMap.ker ψ = (⊥ : Submodule k V₁).prod (LinearMap.ker (g^M)) := by
    rw [hψ, LinearMap.ker_prodMap, LinearMap.ker_id]

  have hrn := LinearMap.finrank_range_add_finrank_ker (ψ.comp S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at hrn
  have hkereq : (LinearMap.ker ψ).comap S.subtype = J.comap S.subtype := by
    rw [hJ, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have hJdim : Module.finrank k ↥((LinearMap.ker ψ).comap S.subtype) =
      Module.finrank k ↥J := by
    rw [hkereq]
    exact (Submodule.comapSubtypeEquivOfLe (hJ ▸ inf_le_left)).finrank_eq
  have hSdim : Module.finrank k ↥S = Module.finrank k ↥T + Module.finrank k ↥J := by
    rw [← hT] at hrn; omega

  have hJT : Disjoint J T := by
    rw [Submodule.disjoint_def]
    rintro ⟨a, b⟩ hJmem hTmem
    obtain ⟨hS, hK⟩ := Submodule.mem_inf.mp hJmem
    rw [hkerψ] at hK
    obtain ⟨ha, hb⟩ := Submodule.mem_prod.mp hK
    obtain ⟨c, hcS, hc⟩ := Submodule.mem_map.mp hTmem
    have hcb : (g^M) c.2 = b := by
      have h := congrArg Prod.snd hc
      simpa [hψ, LinearMap.prodMap_apply] using h
    have hb0 : b = 0 :=
      Submodule.disjoint_def.mp (hN₀ M hM) b hb ⟨c.2, hcb⟩
    have ha0 : a = 0 := (Submodule.mem_bot k).mp ha
    exact Prod.ext ha0 hb0

  have hJle : J ≤ S.map (LinearMap.prodMap (f^M) LinearMap.id) := by
    rintro ⟨a, b⟩ hJmem
    obtain ⟨hS, hK⟩ := Submodule.mem_inf.mp hJmem
    rw [hkerψ] at hK
    obtain ⟨ha, _⟩ := Submodule.mem_prod.mp hK
    have ha0 : a = 0 := (Submodule.mem_bot k).mp ha
    refine ⟨(a, b), hS, ?_⟩
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, ha0, map_zero]

  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq J T
  rw [hJT.eq_bot, finrank_bot] at hGrass
  have hJTdim : Module.finrank k ↥(J ⊔ T) = Module.finrank k ↥S := by omega
  have hbig : J ⊔ T ≤ S.map (LinearMap.prodMap (f^M) LinearMap.id) ⊔
      S.map (LinearMap.prodMap LinearMap.id (g^M)) :=
    sup_le_sup hJle (le_of_eq hT)
  calc Module.finrank k ↥S = Module.finrank k ↥(J ⊔ T) := hJTdim.symm
    _ ≤ _ := Submodule.finrank_mono hbig

variable (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W)

theorem aux_symm_mul : (φ.symm : W →ₗ[k] W) * (φ : W →ₗ[k] W) = 1 :=
  LinearMap.ext fun x => φ.symm_apply_apply x

theorem aux_mul_symm : (φ : W →ₗ[k] W) * (φ.symm : W →ₗ[k] W) = 1 :=
  LinearMap.ext fun x => φ.apply_symm_apply x

theorem pow_symm_pow (M : ℕ) (x : W) :
    ((φ.symm : W →ₗ[k] W) ^ M) (((φ : W →ₗ[k] W) ^ M) x) = x := by
  have hcomm : Commute (φ.symm : W →ₗ[k] W) (φ : W →ₗ[k] W) :=
    (aux_symm_mul φ).trans (aux_mul_symm φ).symm
  have h1 : ((φ.symm : W →ₗ[k] W) ^ M) * ((φ : W →ₗ[k] W) ^ M) = 1 := by
    rw [← hcomm.mul_pow, aux_symm_mul, one_pow]
  calc ((φ.symm:W→ₗ[k]W)^M) (((φ:W→ₗ[k]W)^M) x)
      = (((φ.symm:W→ₗ[k]W)^M) * ((φ:W→ₗ[k]W)^M)) x := rfl
    _ = (1 : W →ₗ[k] W) x := by rw [h1]
    _ = x := rfl

theorem pow_pow_symm (M : ℕ) (x : W) :
    ((φ : W →ₗ[k] W) ^ M) (((φ.symm : W →ₗ[k] W) ^ M) x) = x := by
  have := pow_symm_pow φ.symm M x; simpa using this

theorem barEnd_mkQ (ψ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map ψ ≤ P) (hB : B.map ψ ≤ B) (x : W) (hx : x ∈ B) :
    barEnd ψ P B hP hB ((P.comap B.subtype).mkQ ⟨x, hx⟩) =
      (P.comap B.subtype).mkQ ⟨ψ x, hB ⟨x, hx, rfl⟩⟩ := by
  simp only [barEnd, Submodule.mapQ_apply, Submodule.mkQ_apply]
  rfl

theorem barEnd_pow_mkQ (ψ : W →ₗ[k] W) (P B : Submodule k W)
    (hP : P.map ψ ≤ P) (hB : B.map ψ ≤ B) (M : ℕ) (x : W) (hx : x ∈ B) :
    ((barEnd ψ P B hP hB) ^ M) ((P.comap B.subtype).mkQ ⟨x, hx⟩) =
      (P.comap B.subtype).mkQ ⟨(ψ^M) x, mem_of_pow_map hB M hx⟩ := by
  induction M with
  | zero => simp only [pow_zero]; rfl
  | succ n ih =>
    have hstep : ((barEnd ψ P B hP hB) ^ (n+1)) ((P.comap B.subtype).mkQ ⟨x, hx⟩)
        = (barEnd ψ P B hP hB) (((barEnd ψ P B hP hB) ^ n) ((P.comap B.subtype).mkQ ⟨x, hx⟩)) := by
      rw [pow_succ']; rfl
    have hval : ψ ((ψ^n) x) = (ψ^(n+1)) x := by rw [pow_succ']; rfl
    rw [hstep, ih, barEnd_mkQ]
    exact congrArg _ (Subtype.ext hval)

theorem symm_pow_mem_of_mem_map (M : ℕ) (x : W) (hx : x ∈ B'.map ((φ : W →ₗ[k] W) ^ M)) :
    ((φ.symm : W →ₗ[k] W) ^ M) x ∈ B' := by
  obtain ⟨y, hyB', hy⟩ := hx; rw [← hy, pow_symm_pow]; exact hyB'

def Psi (M : ℕ) :
    ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) →ₗ[k]
      (B ⧸ P.comap B.subtype) × (B' ⧸ P'.comap B'.subtype) :=
  LinearMap.prod
    ((P.comap B.subtype).mkQ ∘ₗ Submodule.inclusion inf_le_left)
    ((P'.comap B'.subtype).mkQ ∘ₗ
      { toFun := fun x => ⟨((φ.symm : W →ₗ[k] W) ^ M) x.1, symm_pow_mem_of_mem_map φ B' M x.1 x.2.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp })

theorem ker_Psi_eq (hPB : P ≤ B) (hP'B' : P' ≤ B') (M : ℕ) :
    LinearMap.ker (Psi φ P B P' B' M) =
      (P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)).comap
        (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)).subtype := by
  ext ⟨x, hx⟩
  have hxB : x ∈ B := hx.1
  have hxB' : x ∈ B'.map ((φ : W →ₗ[k] W) ^ M) := hx.2
  constructor
  · intro hker
    have h1 : (P.comap B.subtype).mkQ ⟨x, hxB⟩ = 0 := congrArg Prod.fst hker
    have h2 : (P'.comap B'.subtype).mkQ
        ⟨((φ.symm:W→ₗ[k]W)^M) x, symm_pow_mem_of_mem_map φ B' M x hxB'⟩ = 0 :=
      congrArg Prod.snd hker
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1 h2
    simp only [mem_comap, coe_subtype] at h1 h2 ⊢
    exact ⟨h1, ((φ.symm:W→ₗ[k]W)^M) x, h2, pow_pow_symm φ M x⟩
  · intro hmem
    simp only [mem_comap, coe_subtype, mem_inf] at hmem
    obtain ⟨h1, y, hyP', hy⟩ := hmem
    have hy' : ((φ.symm:W→ₗ[k]W)^M) x = y := by rw [← hy, pow_symm_pow]
    show Psi φ P B P' B' M ⟨x, hx⟩ = 0
    ext
    · show (P.comap B.subtype).mkQ ⟨x, hxB⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h1
    · show (P'.comap B'.subtype).mkQ ⟨_, _⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [mem_comap, coe_subtype, hy']; exact hyP'

theorem Psi_fst (M : ℕ) (z : ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^M))) :
    (Psi φ P B P' B' M z).1 = (P.comap B.subtype).mkQ ⟨z.1, z.2.1⟩ := rfl

theorem Psi_snd (M : ℕ) (z : ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^M))) :
    (Psi φ P B P' B' M z).2 =
      (P'.comap B'.subtype).mkQ ⟨((φ.symm:W→ₗ[k]W)^M) z.1,
        symm_pow_mem_of_mem_map φ B' M z.1 z.2.2⟩ := rfl

theorem range_Psi_superset
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (M : ℕ) :
    (LinearMap.range (Psi φ P B P' B' 0)).map
        (LinearMap.prodMap ((barEnd (φ : W →ₗ[k] W) P B hP hB) ^ M) LinearMap.id) ⊔
      (LinearMap.range (Psi φ P B P' B' 0)).map
        (LinearMap.prodMap LinearMap.id ((barEnd (φ.symm : W →ₗ[k] W) P' B' hP' hB') ^ M))
      ≤ LinearMap.range (Psi φ P B P' B' M) := by
  have hmap0 : B'.map ((φ:W→ₗ[k]W)^(0:ℕ)) = B' := by
    rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  apply sup_le
  · rintro _ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hx0 : x ∈ B := hx.1
    have hx0' : x ∈ B' := hmap0 ▸ hx.2
    have hφMx : ((φ:W→ₗ[k]W)^M) x ∈ B := mem_of_pow_map hB M hx0
    refine ⟨⟨((φ:W→ₗ[k]W)^M) x, hφMx, x, hx0', rfl⟩, Prod.ext ?_ ?_⟩
    · rw [Psi_fst, LinearMap.prodMap_apply, Psi_fst]
      exact (barEnd_pow_mkQ (φ:W→ₗ[k]W) P B hP hB M x hx.1).symm
    · rw [Psi_snd, LinearMap.prodMap_apply, Psi_snd, LinearMap.id_apply]
      refine congrArg _ (Subtype.ext ?_)
      show ((φ.symm:W→ₗ[k]W)^M) (((φ:W→ₗ[k]W)^M) x) = ((φ.symm:W→ₗ[k]W)^0) x
      rw [pow_symm_pow, pow_zero]; rfl
  · rintro _ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hx0 : x ∈ B := hx.1
    have hx0' : x ∈ B' := hmap0 ▸ hx.2
    have hφMx' : ((φ.symm:W→ₗ[k]W)^M) x ∈ B' := mem_of_pow_map hB' M hx0'
    have hxM : x ∈ B'.map ((φ:W→ₗ[k]W)^M) :=
      ⟨((φ.symm:W→ₗ[k]W)^M) x, hφMx', pow_pow_symm φ M x⟩
    refine ⟨⟨x, hx0, hxM⟩, Prod.ext ?_ ?_⟩
    · rw [Psi_fst, LinearMap.prodMap_apply, Psi_fst, LinearMap.id_apply]
    · rw [Psi_snd, LinearMap.prodMap_apply, Psi_snd]
      have hval0 : ((φ.symm:W→ₗ[k]W)^0) x = x := by rw [pow_zero]; rfl
      have hxval : (⟨((φ.symm:W→ₗ[k]W)^0) x,
          symm_pow_mem_of_mem_map φ B' 0 x hx.2⟩ : ↥B') = ⟨x, hx0'⟩ :=
        Subtype.ext hval0
      rw [congrArg (P'.comap B'.subtype).mkQ hxval]
      exact (barEnd_pow_mkQ (φ.symm:W→ₗ[k]W) P' B' hP' hB' M x hx0').symm

end Ef8d

open Ef8d in
theorem solution
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W) (hPB : P ≤ B) (hP'B' : P' ≤ B')
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (hfin : ∀ M : ℕ, FiniteDimensional k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)))
    (hgen : ∃ M₁ : ℕ, B ≤ ⨆ j : ℕ,
      (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M₁)).map ((φ : W →ₗ[k] W) ^ j))
    (hgen' : ∃ M₁ : ℕ, B' ≤ ⨆ j : ℕ,
      (B' ⊓ B.map ((φ.symm : W →ₗ[k] W) ^ M₁)).map ((φ.symm : W →ₗ[k] W) ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ : W →ₗ[k] W) c y ∈ P)
    (htor' : ∀ y ∈ B', ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ.symm : W →ₗ[k] W) c y ∈ P') :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Module.finrank k ↥(P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)) + Module.finrank k ↥(B ⊓ B') ≤
        Module.finrank k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) +
          Module.finrank k ↥(P ⊓ P') := by
  classical
  obtain ⟨M₁, hM₁⟩ := hgen
  haveI := hfin M₁
  haveI hBP : FiniteDimensional k (B ⧸ P.comap B.subtype) :=
    finiteDimensional_quot_of_monicTorsion (φ:W→ₗ[k]W) P B hP hB
      (B ⊓ B'.map ((φ:W→ₗ[k]W)^M₁)) inf_le_left hM₁ htor
  obtain ⟨M₁', hM₁'⟩ := hgen'
  haveI hfin' : FiniteDimensional k ↥(B' ⊓ B.map ((φ.symm:W→ₗ[k]W)^M₁')) := by
    have e : B' ⊓ B.map ((φ.symm:W→ₗ[k]W)^M₁') =
        (B ⊓ B'.map ((φ:W→ₗ[k]W)^M₁')).map ((φ.symm:W→ₗ[k]W)^M₁') := by
      ext x; simp only [mem_inf, mem_map]
      constructor
      · rintro ⟨hxB', z, hzB, hzx⟩
        refine ⟨((φ:W→ₗ[k]W)^M₁') x, ⟨?_, x, hxB', rfl⟩, pow_symm_pow φ M₁' x⟩
        rw [← hzx, pow_pow_symm]; exact hzB
      · rintro ⟨y, ⟨hyB, z, hzB', hzy⟩, hyx⟩
        refine ⟨?_, y, hyB, hyx⟩
        rw [← hyx, ← hzy, pow_symm_pow]; exact hzB'
    rw [e]; haveI := hfin M₁'; exact Module.Finite.map _ _
  haveI hB'P' : FiniteDimensional k (B' ⧸ P'.comap B'.subtype) :=
    finiteDimensional_quot_of_monicTorsion (φ.symm:W→ₗ[k]W) P' B' hP' hB'
      (B' ⊓ B.map ((φ.symm:W→ₗ[k]W)^M₁')) inf_le_left hM₁' htor'

  have hrank : ∀ M, Module.finrank k ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^M)) =
      Module.finrank k (LinearMap.range (Psi φ P B P' B' M)) +
        Module.finrank k ↥(P ⊓ P'.map ((φ:W→ₗ[k]W)^M)) := by
    intro M; haveI := hfin M
    have hle : P ⊓ P'.map ((φ:W→ₗ[k]W)^M) ≤ B ⊓ B'.map ((φ:W→ₗ[k]W)^M) :=
      inf_le_inf hPB (Submodule.map_mono hP'B')
    have hrn := LinearMap.finrank_range_add_finrank_ker (Psi φ P B P' B' M)
    rw [ker_Psi_eq φ P B P' B' hPB hP'B' M] at hrn
    have heq : Module.finrank k ↥((P ⊓ P'.map ((φ:W→ₗ[k]W)^M)).comap
        (B ⊓ B'.map ((φ:W→ₗ[k]W)^M)).subtype) =
        Module.finrank k ↥(P ⊓ P'.map ((φ:W→ₗ[k]W)^M)) :=
      (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
    omega

  obtain ⟨M₀, hM₀⟩ := fitting_step
    (barEnd (φ:W→ₗ[k]W) P B hP hB) (barEnd (φ.symm:W→ₗ[k]W) P' B' hP' hB')
    (LinearMap.range (Psi φ P B P' B' 0))
  refine ⟨M₀, fun M hM => ?_⟩
  haveI := hfin M; haveI := hfin 0
  have hwin0 : B ⊓ B'.map ((φ:W→ₗ[k]W)^(0:ℕ)) = B ⊓ B' := by
    rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  have hP0 : P ⊓ P'.map ((φ:W→ₗ[k]W)^(0:ℕ)) = P ⊓ P' := by
    rw [pow_zero, show (1:W→ₗ[k]W) = LinearMap.id from rfl, Submodule.map_id]
  have h0' := hrank 0
  have hB0 : Module.finrank k ↥(B ⊓ B') =
      Module.finrank k ↥(B ⊓ B'.map ((φ:W→ₗ[k]W)^(0:ℕ))) := by rw [hwin0]
  have hP0' : Module.finrank k ↥(P ⊓ P') =
      Module.finrank k ↥(P ⊓ P'.map ((φ:W→ₗ[k]W)^(0:ℕ))) := by rw [hP0]
  have hMr := hrank M
  have hI : Module.finrank k ↥(LinearMap.range (Psi φ P B P' B' 0)) ≤
      Module.finrank k ↥(LinearMap.range (Psi φ P B P' B' M)) :=
    (hM₀ M hM).trans (Submodule.finrank_mono (range_Psi_superset φ P B P' B' hP hB hP' hB' M))
  omega

end
end S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le
end P2MW
export P2MW.S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le (solution)
