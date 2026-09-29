-- Prove2me | solution 1 for LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e207bbf2-6b6e-5770-b52f-d8fb0fa28ae8

import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_LocalLanglands_PadicHeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd

set_option autoImplicit false
set_option Elab.async false

open NumberField IsDedekindDomain AutomorphicForm AdelicDock LocalGL2 HeckeIntegralSeam
open NumberField.AdelicLevel

namespace P1BRowsHsys

theorem isHeckeCosetSystem_congr_gen {G : Type*} [Group G] {U : Subgroup G} {g g' : G}
    {ι : Type*} {reps : ι → G}
    (hgg' : HeckePair.doubleCoset U g' = HeckePair.doubleCoset U g)
    (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g' reps where
  mem_doubleCoset i := hgg' ▸ h.mem_doubleCoset i
  covers x hx := h.covers x (hgg' ▸ hx)
  mk_injective := h.mk_injective

theorem padicPlace_coe (p : Nat.Primes) :
    @padicPlace (p : ℕ) ⟨p.prop⟩ = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p := rfl

theorem padicPlace_primesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    @padicPlace ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ))
      ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).prop⟩ = v := by
  rw [padicPlace_coe]
  exact Equiv.symm_apply_apply _ _

example (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)
      = Rat.HeightOneSpectrum.natGenerator v := rfl

theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ) := by
  have e : (𝓞 ℚ ⧸ v.asIdeal) ≃+*
      (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)}) :=
    Ideal.quotientEquiv _ _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
      (by rw [Ideal.map_coe]; exact Rat.HeightOneSpectrum.span_natGenerator v)
  have h1 : Ideal.absNorm v.asIdeal = Nat.card (𝓞 ℚ ⧸ v.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h2 : Nat.card (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)})
      = Rat.HeightOneSpectrum.natGenerator v := by
    rw [Nat.card_congr (Int.quotientSpanEquivZMod _).toEquiv]
    exact Nat.card_zmod _
  rw [h1, Nat.card_congr e.toEquiv, h2]
  rfl

theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 ℚ)} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ¬ v.asIdeal ∣ N) {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) :
    IsLocalLevelOne (𝓞 ℚ) ℚ v N m := by
  have hN : N ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have hb : NumberField.AdelicLevel.idealBound (𝓞 ℚ) N v = 1 :=
    NumberField.AdelicLevel.idealBound_eq_one_of_not_dvd hN hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
      (sub_mem (hm 1 1) (one_mem _))

theorem padicGL_mem_localLevelOne_of_integral {N : Ideal (𝓞 ℚ)} (p : ℕ) [Fact p.Prime]
    (hv : ¬ (padicPlace p).asIdeal ∣ N) {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ integralSubgroup ℤ_[p] ℚ_[p]) :
    padicGL p k ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace p) N := by
  have hint : ∀ (j : GL (Fin 2) ℚ_[p]), j ∈ integralSubgroup ℤ_[p] ℚ_[p] →
      ∀ a b : Fin 2, (padicGL p j : Matrix (Fin 2) (Fin 2) _) a b
        ∈ (padicPlace p).adicCompletionIntegers ℚ := by
    rintro j ⟨y, rfl⟩ a b
    rw [padicGL_apply, Matrix.GeneralLinearGroup.map_apply]
    exact padicRingEquiv_coe_mem p _
  rw [mem_localLevelOne_iff]
  refine ⟨isLocalLevelOne_of_integral hv (hint k hk), ?_⟩
  rw [← map_inv]
  exact isLocalLevelOne_of_integral hv (hint k⁻¹ (inv_mem hk))

theorem padicToAdelic_mem_compactU {N : Ideal (𝓞 ℚ)} (p : ℕ) [Fact p.Prime]
    (hv : ¬ (padicPlace p).asIdeal ∣ N) {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ integralSubgroup ℤ_[p] ℚ_[p]) :
    padicToAdelic p k ∈ (productionPinsCompact ℚ).U N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  ·
    rw [padicToAdelic_apply, finEmbed_mem_levelOne_iff, padicToFinAdelic_apply,
      localEmbed_mem_finiteLevelOne_iff]
    exact padicGL_mem_localLevelOne_of_integral p hv hk
  ·
    show _ ∈ finiteAdelicGL2Subgroup ℚ
    rw [finiteAdelicGL2Subgroup, MonoidHom.mem_ker, padicToAdelic_apply]
    exact glArch_finEmbed _ _ _

theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace p) = p := by
  show (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (padicPlace p) : ℕ) = p
  rw [padicPlace, Equiv.apply_symm_apply]

theorem ratLevel_eq_asIdeal (p : ℕ) [Fact p.Prime] :
    ratLevel p = (padicPlace p).asIdeal := by
  have e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hmap : (ratLevel p).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
      = (padicPlace p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    rw [← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_padicPlace, ratLevel,
      Ideal.map_span, Set.image_singleton, map_natCast]
  have := congrArg (Ideal.comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ)) hmap
  rwa [Ideal.comap_coe, Ideal.comap_coe,
    Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective,
    Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective] at this

theorem valued_padicRingEquiv_natCast (p : ℕ) [Fact p.Prime] :
    Valued.v (padicRingEquiv p ((p : ℕ) : ℚ_[p])) = WithZero.exp (-1 : ℤ) := by
  have h0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← idealBound_ratLevel p h0, ratLevel_eq_asIdeal,
    NumberField.AdelicLevel.idealBound_of_ne_bot (padicPlace p).ne_bot]
  congr 1
  have hirr : Irreducible (Associates.mk (padicPlace p).asIdeal) :=
    (Associates.irreducible_mk).mpr
      (Ideal.prime_of_isPrime (padicPlace p).ne_bot (padicPlace p).isPrime).irreducible
  rw [Associates.count_self hirr]
  norm_num

noncomputable def padicPUnit (p : ℕ) [Fact p.Prime] : ((padicPlace p).adicCompletion ℚ)ˣ :=
  Units.map (padicRingEquiv p).toRingHom.toMonoidHom
    (Units.mk0 ((p : ℕ) : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

theorem valued_padicPUnit (p : ℕ) [Fact p.Prime] :
    Valued.v ((padicPUnit p : ((padicPlace p).adicCompletion ℚ)ˣ) :
      (padicPlace p).adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
  valued_padicRingEquiv_natCast p

theorem glArch_heckeGenAt {v : HeightOneSpectrum (𝓞 ℚ)} (t : (v.adicCompletion ℚ)ˣ) :
    NumberField.AdelicLevel.glArch (𝓞 ℚ) ℚ (NumberField.AdelicLevel.heckeGenAt (𝓞 ℚ) ℚ v t)
      = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((NumberField.AdelicLevel.heckeGenAt (𝓞 ℚ) ℚ v t :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = _
  rw [NumberField.AdelicLevel.heckeGenAt_fst]
  rfl

theorem padicToAdelic_padicDiagP (p : ℕ) [Fact p.Prime] :
    padicToAdelic p (padicDiagP p)
      = NumberField.AdelicLevel.heckeGenAt (𝓞 ℚ) ℚ (padicPlace p) (padicPUnit p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine Prod.ext ?_ ?_
  ·
    rw [NumberField.AdelicLevel.heckeGenAt_fst]
    have h1 := glArch_padicToAdelic p (padicDiagP p)
    have h2 := congrArg (fun (g : GL (Fin 2) (InfiniteAdeleRing ℚ)) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) h1
    exact h2
  ·
    ext w : 1
    by_cases hw : w = padicPlace p
    · subst hw
      rw [NumberField.AdelicLevel.heckeGenAt_snd_apply_self]
      show (localMat (𝓞 ℚ) ℚ (padicPlace p) (padicGL p (padicDiagP p) :
          Matrix (Fin 2) (Fin 2) _) i j) (padicPlace p) = _
      rw [localMat_apply_self, padicGL_apply, coe_diagPi]
      fin_cases i <;> fin_cases j <;>
        simp [padicPUnit, Matrix.diagonal, padicRingEquiv_apply] <;> try rfl
    · rw [NumberField.AdelicLevel.heckeGenAt_snd_apply_of_ne _ hw]
      show (localMat (𝓞 ℚ) ℚ (padicPlace p) (padicGL p (padicDiagP p) :
          Matrix (Fin 2) (Fin 2) _) i j) w = _
      rw [localMat_apply_of_ne _ _ _ _ i j hw]

theorem heckeGen_inv_mul_docked_mem_U {N : Ideal (𝓞 ℚ)} (p : ℕ) [Fact p.Prime] :
    (NumberField.AdelicLevel.heckeGen (𝓞 ℚ) ℚ (padicPlace p))⁻¹
        * padicToAdelic p (padicDiagP p) ∈ (productionPinsCompact ℚ).U N := by
  rw [padicToAdelic_padicDiagP]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact NumberField.AdelicLevel.heckeGen_inv_mul_heckeGenAt_mem_levelOne
      (padicPUnit p) (valued_padicPUnit p) N
  · show _ ∈ finiteAdelicGL2Subgroup ℚ
    rw [finiteAdelicGL2Subgroup, MonoidHom.mem_ker, map_mul, map_inv]
    rw [show NumberField.AdelicLevel.heckeGen (𝓞 ℚ) ℚ (padicPlace p)
        = NumberField.AdelicLevel.heckeGenAt (𝓞 ℚ) ℚ (padicPlace p)
            (NumberField.AdelicLevel.uniformizerUnit ℚ (padicPlace p)) from rfl,
      glArch_heckeGenAt, glArch_heckeGenAt, inv_one, one_mul]

theorem doubleCoset_eq_of_inv_mul_mem {G : Type*} [Group G] {U : Subgroup G} {g g' : G}
    (h : g⁻¹ * g' ∈ U) : HeckePair.doubleCoset U g' = HeckePair.doubleCoset U g := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff, HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, (g⁻¹ * g') * w, U.mul_mem h hw, by group⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, (g'⁻¹ * g) * w, U.mul_mem (by simpa using U.inv_mem h) hw, by group⟩

theorem mem_compactU_of_components {N : Ideal (𝓞 ℚ)} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (harch : glArch (𝓞 ℚ) ℚ h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ h) ∈ localLevelOne (𝓞 ℚ) ℚ w N) :
    h ∈ (productionPinsCompact ℚ).U N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 ℚ) ℚ w N
          (finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 ℚ) ℚ w N
          ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ h))⁻¹ : GL (Fin 2) _) := by
      intro w
      have := (mem_localLevelOne_iff (𝓞 ℚ) ℚ w (finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ h))).mp
        (hfin w)
      exact this
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · show _ ∈ finiteAdelicGL2Subgroup ℚ
    rw [finiteAdelicGL2Subgroup, MonoidHom.mem_ker]
    exact harch

theorem components_of_mem_compactU {N : Ideal (𝓞 ℚ)} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hh : h ∈ (productionPinsCompact ℚ).U N) :
    glArch (𝓞 ℚ) ℚ h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ h) ∈ localLevelOne (𝓞 ℚ) ℚ w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

theorem mem_integralSubgroup_of_norm_le {p : ℕ} [Fact p.Prime] {k : GL (Fin 2) ℚ_[p]}
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1) :
    k ∈ integralSubgroup ℤ_[p] ℚ_[p] := by
  set A : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j => ⟨(k : Matrix _ _ _) i j, hk i j⟩ with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j => ⟨((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix _ _ _) i j, hk' i j⟩ with hB
  have hmapA : A.map (algebraMap ℤ_[p] ℚ_[p]) = (k : Matrix _ _ _) := by
    ext i j; simp [hA, PadicInt.algebraMap_apply]
  have hmapB : B.map (algebraMap ℤ_[p] ℚ_[p]) = ((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix _ _ _) := by
    ext i j; simp [hB, PadicInt.algebraMap_apply]
  have hinj : Function.Injective ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix :
      Matrix (Fin 2) (Fin 2) ℤ_[p] →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    intro x y hxy
    ext i j
    have h2 : ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix x) i j
        = ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix y) i j := by rw [hxy]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, PadicInt.algebraMap_apply] at h2
    exact Subtype.coe_injective h2
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, map_one]
    show A.map _ * B.map _ = 1
    rw [hmapA, hmapB]
    exact_mod_cast Units.mul_inv k
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, map_one]
    show B.map _ * A.map _ = 1
    rw [hmapA, hmapB]
    exact_mod_cast Units.inv_mul k
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  show A.map _ = _
  exact hmapA

theorem finComponent_glFin_padicToAdelic (p : ℕ) [Fact p.Prime] (z : GL (Fin 2) ℚ_[p]) :
    finComponent (𝓞 ℚ) ℚ (padicPlace p) (glFin (𝓞 ℚ) ℚ (padicToAdelic p z)) = padicGL p z := by
  rw [glFin_padicToAdelic, finComponent_padicToFinAdelic_self]

theorem finComponent_glFin_padicToAdelic_of_ne (p : ℕ) [Fact p.Prime] (z : GL (Fin 2) ℚ_[p])
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ padicPlace p) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (padicToAdelic p z)) = 1 := by
  rw [glFin_padicToAdelic, finComponent_padicToFinAdelic_of_ne p z hw]

theorem exists_padicGL_eq_of_mem_localLevelOne {N : Ideal (𝓞 ℚ)} (p : ℕ) [Fact p.Prime]
    {k : GL (Fin 2) ((padicPlace p).adicCompletion ℚ)}
    (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace p) N) :
    ∃ y ∈ integralSubgroup ℤ_[p] ℚ_[p], padicGL p y = k := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_iff (𝓞 ℚ) ℚ (padicPlace p) k).mp hk
  refine ⟨Matrix.GeneralLinearGroup.map (padicRingEquiv p).symm.toRingHom k, ?_, ?_⟩
  · refine mem_integralSubgroup_of_norm_le (fun i j => ?_) (fun i j => ?_)
    · rw [Matrix.GeneralLinearGroup.map_apply]
      refine (norm_le_one_iff_mem p _).mpr ?_
      rw [show padicRingEquiv p ((padicRingEquiv p).symm.toRingHom ((k : Matrix _ _ _) i j))
          = (k : Matrix _ _ _) i j from (padicRingEquiv p).apply_symm_apply _]
      exact h1.integral i j
    · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
      refine (norm_le_one_iff_mem p _).mpr ?_
      rw [show padicRingEquiv p ((padicRingEquiv p).symm.toRingHom
            (((k⁻¹ : GL (Fin 2) _) : Matrix _ _ _) i j))
          = ((k⁻¹ : GL (Fin 2) _) : Matrix _ _ _) i j from (padicRingEquiv p).apply_symm_apply _]
      exact h2.integral i j
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [padicGL_apply, Matrix.GeneralLinearGroup.map_apply]
    exact (padicRingEquiv p).apply_symm_apply _

theorem mem_integralSubgroup_of_padicGL_mem_localLevelOne {N : Ideal (𝓞 ℚ)} (p : ℕ)
    [Fact p.Prime] {z : GL (Fin 2) ℚ_[p]}
    (hz : padicGL p z ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace p) N) :
    z ∈ integralSubgroup ℤ_[p] ℚ_[p] := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_iff (𝓞 ℚ) ℚ (padicPlace p) _).mp hz
  refine mem_integralSubgroup_of_norm_le (fun i j => ?_) (fun i j => ?_)
  · refine (norm_le_one_iff_mem p _).mpr ?_
    have := h1.integral i j
    rwa [padicGL_apply] at this
  · refine (norm_le_one_iff_mem p _).mpr ?_
    have := h2.integral i j
    rwa [← map_inv, padicGL_apply] at this

theorem isHeckeCosetSystem_docked {N : Ideal (𝓞 ℚ)} (p : ℕ) [Fact p.Prime]
    (hv : ¬ (padicPlace p).asIdeal ∣ N) :
    IsHeckeCosetSystem ((productionPinsCompact ℚ).U N)
      (padicToAdelic p (padicDiagP p))
      (fun i => padicToAdelic p (padicHeckeRep p i)) := by
  have S := isHeckeCosetSystem_padicHeckeRep p
  constructor
  ·
    intro i
    obtain ⟨u, hu, u', hu', heq⟩ := HeckePair.mem_doubleCoset_iff.mp (S.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨padicToAdelic p u, padicToAdelic_mem_compactU p hv hu,
       padicToAdelic p u', padicToAdelic_mem_compactU p hv hu', ?_⟩
    rw [← map_mul, ← map_mul, heq]
  ·
    intro z hz
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hz
    obtain ⟨harch₁, hfin₁⟩ := components_of_mem_compactU hu₁
    obtain ⟨y₁, hy₁, hy₁eq⟩ := exists_padicGL_eq_of_mem_localLevelOne p (hfin₁ (padicPlace p))
    have hylocal : y₁ * padicDiagP p ∈ HeckePair.doubleCoset (integralSubgroup ℤ_[p] ℚ_[p])
        (padicDiagP p) :=
      HeckePair.mem_doubleCoset_iff.mpr ⟨y₁, hy₁, 1, one_mem _, by rw [mul_one]⟩
    obtain ⟨i₀, hi₀⟩ := S.covers _ hylocal

    have habs : (QuotientGroup.mk (u₁ * padicToAdelic p (padicDiagP p) * u₂) :
        _ ⧸ (productionPinsCompact ℚ).U N)
        = QuotientGroup.mk (u₁ * padicToAdelic p (padicDiagP p)) := by
      rw [QuotientGroup.eq]
      simpa [mul_inv_rev, mul_assoc] using ((productionPinsCompact ℚ).U N).inv_mem hu₂
    have hloc : (y₁ * padicDiagP p)⁻¹ * padicHeckeRep p i₀ ∈ integralSubgroup ℤ_[p] ℚ_[p] :=
      QuotientGroup.eq.mp hi₀
    have hkey : ((u₁ * padicToAdelic p (padicDiagP p))⁻¹
        * padicToAdelic p (padicHeckeRep p i₀)) ∈ (productionPinsCompact ℚ).U N := by
      refine mem_compactU_of_components ?_ ?_
      · simp only [map_mul, map_inv, mul_inv_rev, glArch_padicToAdelic, harch₁]
        simp
      · intro w
        by_cases hw : w = padicPlace p
        · subst hw
          have hloc2 : padicGL p ((y₁ * padicDiagP p)⁻¹ * padicHeckeRep p i₀)
              ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace p) N :=
            padicGL_mem_localLevelOne_of_integral p hv hloc
          have hgoal_eq : finComponent (𝓞 ℚ) ℚ (padicPlace p) (glFin (𝓞 ℚ) ℚ
              ((u₁ * padicToAdelic p (padicDiagP p))⁻¹ * padicToAdelic p (padicHeckeRep p i₀)))
              = padicGL p ((y₁ * padicDiagP p)⁻¹ * padicHeckeRep p i₀) := by
            simp only [map_mul, map_inv, mul_inv_rev, finComponent_glFin_padicToAdelic,
              ← hy₁eq]
          rw [hgoal_eq]
          exact hloc2
        · have hgone : finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
              ((u₁ * padicToAdelic p (padicDiagP p))⁻¹ * padicToAdelic p (padicHeckeRep p i₀)))
              = (finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ u₁))⁻¹ := by
            simp only [map_mul, map_inv, mul_inv_rev,
              finComponent_glFin_padicToAdelic_of_ne p _ hw]
            simp
          rw [hgone]
          exact Subgroup.inv_mem _ (hfin₁ w)
    exact ⟨i₀, habs.trans (QuotientGroup.eq.mpr hkey)⟩
  ·
    intro i j hij
    rw [QuotientGroup.eq] at hij
    rw [← map_inv, ← map_mul] at hij
    have := (components_of_mem_compactU hij).2 (padicPlace p)
    rw [finComponent_glFin_padicToAdelic] at this
    have hmem := mem_integralSubgroup_of_padicGL_mem_localLevelOne p this
    exact S.mk_injective (QuotientGroup.eq.mpr hmem)

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι ι' : Type*} {reps : ι → G} (e : ι' ≃ ι)
    (h : IsHeckeCosetSystem U g reps) : IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := h.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective i j hij := e.injective (h.mk_injective hij)

theorem absNorm_padicPlace (p : ℕ) [Fact p.Prime] :
    Ideal.absNorm (padicPlace p).asIdeal = p := by
  rw [absNorm_asIdeal]
  show Rat.HeightOneSpectrum.natGenerator (padicPlace p) = p
  exact natGenerator_padicPlace p

theorem exists_heckeCosetSystem_at_padicPlace {N : Ideal (𝓞 ℚ)} (p : ℕ) [Fact p.Prime]
    (hv : ¬ (padicPlace p).asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm (padicPlace p).asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      IsHeckeCosetSystem ((productionPinsCompact ℚ).U N)
        ((productionPinsCompact ℚ).gen (padicPlace p)) reps := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have ecard : Fintype.card (Fin (Ideal.absNorm (padicPlace p).asIdeal + 1))
      = Fintype.card (Option (ZMod p)) := by
    simp [absNorm_padicPlace p, ZMod.card]
  refine ⟨(fun i => padicToAdelic p (padicHeckeRep p i)) ∘ Fintype.equivOfCardEq ecard, ?_⟩
  have hdock := isHeckeCosetSystem_docked p hv
  have hdc : HeckePair.doubleCoset ((productionPinsCompact ℚ).U N)
        ((productionPinsCompact ℚ).gen (padicPlace p))
      = HeckePair.doubleCoset ((productionPinsCompact ℚ).U N)
        (padicToAdelic p (padicDiagP p)) := by
    rw [show (productionPinsCompact ℚ).gen (padicPlace p)
        = NumberField.AdelicLevel.heckeGen (𝓞 ℚ) ℚ (padicPlace p) from rfl]
    exact (doubleCoset_eq_of_inv_mul_mem (heckeGen_inv_mul_docked_mem_U p)).symm
  exact isHeckeCosetSystem_comp_equiv _ (isHeckeCosetSystem_congr_gen hdc hdock)

theorem exists_heckeCosetSystem_productionPinsCompact_of_not_dvd_impl
    (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      IsHeckeCosetSystem ((productionPinsCompact ℚ).U N)
        ((productionPinsCompact ℚ).gen v) reps := by
  haveI : Fact ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).prop⟩
  rw [← padicPlace_primesEquiv v] at hv ⊢
  exact exists_heckeCosetSystem_at_padicPlace _ hv

end P1BRowsHsys

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm

theorem solution
    (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsCompact ℚ).U N)
        ((productionPinsCompact ℚ).gen v) reps := by
  first
    | exact P1BRowsHsys.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd_impl N v hv
    | (apply P1BRowsHsys.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd_impl <;> assumption)

end S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd
end P2MW
export P2MW.S_LanglandsTunnell_exists_heckeCosetSystem_productionPinsCompact_of_not_dvd (solution)
